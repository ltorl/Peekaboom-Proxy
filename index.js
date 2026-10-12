// Peekaboom (Node): serves any public site so it can be embedded in an <iframe>.
//
//   node index.js              (Node 20+, no dependencies; PORT=8787 HOST=0.0.0.0 by default)
//   <iframe src="https://<host>/__px/https://example.com/"></iframe>
//
// Everything is in this one file: the HTTP server, the proxy, a small HTML
// rewriter and the script injected into every page. cloudflare.js is the same
// proxy as a Cloudflare Worker.
import http from 'node:http';
import https from 'node:https';
import net from 'node:net';
import zlib from 'node:zlib';
import tls from 'node:tls';
import dns from 'node:dns/promises';
import { Readable } from 'node:stream';
import vm from 'node:vm';

const PORT = Number(process.env.PORT) || 8787;
const HOST = process.env.HOST || '0.0.0.0';
const PREFIX = '/__px/';
const ORIGIN_COOKIE = '__px_origin';
const UPSTREAM_TIMEOUT_MS = 100_000; // time to response headers; slow origins can take 30s+
const MAX_BUFFERED_BYTES = 16 * 1024 * 1024; // HTML / CSS rewriting buffers the body

const DROP_REQUEST_HEADERS = new Set([
  'host', 'connection', 'keep-alive', 'proxy-connection', 'te', 'trailer', 'transfer-encoding',
  'accept-encoding', 'origin', 'referer', 'cookie', 'cdn-loop', 'x-real-ip', 'x-forwarded-for',
  'x-forwarded-proto', 'x-forwarded-host', 'true-client-ip', 'upgrade', 'expect',
]);

const DROP_RESPONSE_HEADERS = [
  'content-security-policy', 'content-security-policy-report-only', 'x-frame-options',
  'cross-origin-opener-policy', 'cross-origin-embedder-policy', 'cross-origin-resource-policy',
  'strict-transport-security', 'clear-site-data', 'report-to', 'reporting-endpoints', 'nel',
  'alt-svc', 'link', 'permissions-policy', 'origin-agent-cluster', 'referrer-policy',
  'access-control-allow-origin', 'access-control-allow-credentials',
];

// ---------------------------------------------------------------- upstream connections

// Unlike a Cloudflare Worker, a Node server can reach your private network, so refuse
// hostnames that resolve to private, loopback or link-local addresses.
async function checkHost(hostname) {
  let addrs;
  try {
    addrs = await dns.lookup(hostname, { all: true, verbatim: true });
  } catch {
    return null; // let fetch report the DNS failure
  }
  return addrs.some((a) => isPrivate(a.address)) ? `${hostname} resolves to a private address.` : null;
}

function isPrivate(ip) {
  if (net.isIPv4(ip)) {
    const [a, b] = ip.split('.').map(Number);
    return a === 0 || a === 10 || a === 127 || a >= 224 ||
      (a === 100 && b >= 64 && b <= 127) || (a === 169 && b === 254) ||
      (a === 172 && b >= 16 && b <= 31) || (a === 192 && b === 168) || (a === 198 && (b === 18 || b === 19));
  }
  const v = ip.toLowerCase();
  if (v.startsWith('::ffff:')) return isPrivate(v.slice(7));
  return v === '::' || v === '::1' || /^f[cd]/.test(v) || /^fe[89ab]/.test(v) || v.startsWith('ff');
}

// Refuse private addresses at connect time too, so DNS rebinding can't slip past checkHost.
function safeLookup(hostname, options, callback) {
  dns.lookup(hostname, { ...options, all: true }).then((addrs) => {
    const bad = addrs.find((a) => isPrivate(a.address));
    if (bad) return callback(new Error(`${hostname} resolves to a private address.`));
    if (options.all) return callback(null, addrs);
    callback(null, addrs[0].address, addrs[0].family);
  }, callback);
}

const agentOpts = { keepAlive: true, lookup: safeLookup };
const agents = { 'http:': new http.Agent(agentOpts), 'https:': new https.Agent(agentOpts) };

const ENCODINGS = ['gzip', 'deflate', 'br', ...(zlib.createZstdDecompress ? ['zstd'] : [])];
const DECODERS = {
  gzip: () => zlib.createGunzip(),
  'x-gzip': () => zlib.createGunzip(),
  deflate: () => zlib.createInflate(),
  br: () => zlib.createBrotliDecompress(),
  zstd: () => zlib.createZstdDecompress(),
};

// fetch() replacement built on node:http(s). Node's global fetch rewrites
// sec-fetch-mode to "cors" and adds its own defaults, which makes many sites
// treat page loads as API calls; this sends the browser's headers as given.
function nodeFetch(url, init = {}) {
  return new Promise((resolve, reject) => {
    const u = new URL(url);
    const headers = {};
    for (const [k, v] of new Headers(init.headers)) headers[k] = v;
    headers['accept-encoding'] = ENCODINGS.join(', ');

    const req = (u.protocol === 'https:' ? https : http).request(u, {
      method: init.method || 'GET',
      headers,
      agent: agents[u.protocol],
      signal: init.signal,
    });
    req.on('error', reject);
    req.on('response', (res) => {
      const out = new Headers();
      for (let i = 0; i < res.rawHeaders.length; i += 2) {
        try { out.append(res.rawHeaders[i], res.rawHeaders[i + 1]); } catch {}
      }
      const noBody = init.method === 'HEAD' || [204, 205, 304].includes(res.statusCode);
      let body = res;
      const enc = (out.get('content-encoding') || '').trim().toLowerCase();
      if (!noBody && DECODERS[enc]) {
        body = res.pipe(DECODERS[enc]());
        res.on('error', (e) => body.destroy(e));
        out.delete('content-encoding');
      }
      if (noBody) res.resume();
      const status = res.statusCode < 200 ? 502 : res.statusCode;
      resolve(new Response(noBody ? null : Readable.toWeb(body), {
        status, statusText: res.statusMessage || '', headers: out,
      }));
    });
    if (init.body) Readable.fromWeb(init.body).on('error', (e) => req.destroy(e)).pipe(req);
    else req.end();
  });
}

// ---------------------------------------------------------------- request handling

async function handle(request) {
  try {
    const r = await resolveTarget(request);
    return r.response || await proxy(request, r.self, r.target);
  } catch (err) {
    return errorPage(500, 'Proxy error', errText(err));
  }
}

// Works out which upstream URL a request is for: { self, target } or { response }.
async function resolveTarget(request) {
  const url = new URL(request.url);

  // Convenience entry point: /?url=example.com
  if (url.pathname === '/' && url.searchParams.has('url')) {
    const target = normalizeInput(url.searchParams.get('url'));
    if (!target) return { response: errorPage(400, 'Invalid URL', 'Pass a public http(s) URL.') };
    return { response: Response.redirect(url.origin + PREFIX + target.href, 302) };
  }

  if (url.pathname === '/__px_sw.js') return { response: serviceWorkerResponse() };

  let target;
  if (url.pathname.startsWith(PREFIX)) {
    const raw = url.pathname.slice(PREFIX.length).replace(/^([a-z]+):\/(?!\/)/i, '$1://') + url.search;
    try { target = new URL(raw); } catch {
      return { response: errorPage(400, 'Invalid URL', raw) };
    }
  } else {
    // A request that escaped rewriting (e.g. "/assets/app.js"): work out which
    // site it belongs to from the Referer, then the origin cookie.
    const origin = originFromReferer(request, url) || originFromCookie(request);
    if (!origin) return { response: usagePage(url) };
    target = new URL(url.pathname + url.search, origin);
  }

  if (target.protocol === 'wss:') target.protocol = 'https:';
  if (target.protocol === 'ws:') target.protocol = 'http:';
  const blocked = blockedReason(target, url) || (await checkHost(target.hostname));
  if (blocked) return { response: errorPage(403, 'Blocked', blocked) };

  return { self: url, target };
}

// Headers to send upstream: hop-by-hop and identifying headers dropped,
// Origin / Referer translated back to the upstream site.
function upstreamHeaders(request, self, target) {
  const headers = new Headers();
  for (const [k, v] of request.headers) {
    if (!DROP_REQUEST_HEADERS.has(k) && !k.startsWith('cf-')) headers.set(k, v);
  }
  const cookie = (request.headers.get('cookie') || '')
    .split(/;\s*/).filter((c) => c && !c.startsWith(ORIGIN_COOKIE + '=')).join('; ');
  if (cookie) headers.set('cookie', cookie);

  const refUp = upstreamFromProxied(request.headers.get('referer'), self);
  if (refUp) headers.set('referer', refUp.href);
  if (request.headers.has('origin')) headers.set('origin', refUp ? refUp.origin : target.origin);
  return headers;
}

const errText = (err) => String((err && err.cause && err.cause.message) || (err && err.message) || err);

function normalizeInput(input) {
  let s = (input || '').trim();
  if (!s) return null;
  if (!/^[a-z][a-z0-9+.-]*:\/\//i.test(s)) s = 'https://' + s;
  try {
    const u = new URL(s);
    return /^https?:$/.test(u.protocol) ? u : null;
  } catch {
    return null;
  }
}

function upstreamFromProxied(href, self) {
  const p = self.origin + PREFIX;
  if (!href || !href.startsWith(p)) return null;
  try { return new URL(href.slice(p.length)); } catch { return null; }
}

function originFromReferer(request, self) {
  const up = upstreamFromProxied(request.headers.get('referer'), self);
  return up && up.origin;
}

function originFromCookie(request) {
  const m = (request.headers.get('cookie') || '').match(new RegExp(`(?:^|;\\s*)${ORIGIN_COOKIE}=([^;]+)`));
  if (!m) return null;
  try {
    const u = new URL(decodeURIComponent(m[1]));
    return /^https?:$/.test(u.protocol) ? u.origin : null;
  } catch {
    return null;
  }
}

function blockedReason(u, self) {
  const h = u.hostname.toLowerCase();
  if (!/^https?:$/.test(u.protocol)) return 'Only http and https URLs can be proxied.';
  if (h === 'localhost' || /\.(localhost|local|internal|lan|home\.arpa)$/.test(h) || !h.includes('.')) {
    return 'Local and internal hostnames cannot be proxied.';
  }
  if (/^[\d.]+$/.test(h) || h.startsWith('[') || h.includes(':')) return 'IP addresses cannot be proxied.';
  if (h === self.hostname) return 'The proxy cannot proxy itself.';
  return null;
}

// ---------------------------------------------------------------- URL rewriting

const SKIP_URL = /^(data|blob|javascript|about|mailto|tel|sms):/i;

// Any URL -> /__px/<absolute upstream URL>
function proxUrl(value, base) {
  const s = value.trim();
  if (!s || s[0] === '#' || s.startsWith(PREFIX) || SKIP_URL.test(s)) return value;
  let abs;
  try { abs = new URL(s, base); } catch { return value; }
  if (!/^(https?|wss?):$/.test(abs.protocol)) return value;
  return PREFIX + abs.href;
}

// Navigational links keep real paths for same-site targets so client-side
// routers see them; the runtime routes the click through the proxy.
function proxLink(value, base, upstream) {
  const s = value.trim();
  if (!s || s[0] === '#' || s.startsWith(PREFIX) || SKIP_URL.test(s)) return value;
  let abs;
  try { abs = new URL(s, base); } catch { return value; }
  if (!/^https?:$/.test(abs.protocol)) return value;
  if (abs.origin === upstream.origin) return abs.pathname + abs.search + abs.hash;
  return PREFIX + abs.href;
}

function proxSrcset(value, base) {
  return value.split(/,\s+/).map((part) => {
    const m = part.trim().match(/^(\S+)(\s+.*)?$/);
    return m ? proxUrl(m[1], base) + (m[2] || '') : part;
  }).join(', ');
}

function rewriteCss(css, base) {
  return css
    .replace(/url\(\s*(['"]?)([^'")]+)\1\s*\)/gi, (m, q, u) => `url(${q}${proxUrl(u, base)}${q})`)
    .replace(/@import\s+(['"])([^'"]+)\1/gi, (m, q, u) => `@import ${q}${proxUrl(u, base)}${q}`);
}

function rewriteRefresh(value, base) {
  return value.replace(/(url\s*=\s*['"]?)([^'";]+)/i, (m, pre, u) => pre + proxUrl(u, base));
}

// ---------------------------------------------------------------- proxy

async function proxy(request, self, target) {
  const headers = upstreamHeaders(request, self, target);

  if (request.headers.get('service-worker') === 'script') {
    return new Response('Service workers are disabled by the proxy', { status: 404 });
  }

  const ctrl = new AbortController();
  const timer = setTimeout(() => ctrl.abort(), UPSTREAM_TIMEOUT_MS);
  let resp;
  try {
    resp = await nodeFetch(target.href, {
      method: request.method,
      headers,
      body: ['GET', 'HEAD'].includes(request.method) ? undefined : request.body,
      redirect: 'manual',
      signal: ctrl.signal,
      duplex: 'half',
    });
  } catch (err) {
    const timedOut = ctrl.signal.aborted;
    return errorPage(timedOut ? 504 : 502, timedOut ? 'Site timed out' : 'Could not reach site',
      `${target.href}\n${timedOut ? `No response within ${UPSTREAM_TIMEOUT_MS / 1000}s.` : errText(err)}`);
  } finally {
    clearTimeout(timer);
  }

  const out = new Headers(resp.headers);
  for (const h of DROP_RESPONSE_HEADERS) out.delete(h);
  // nodeFetch has already decompressed the body, so the original framing no longer applies.
  const length = Number(out.get('content-length') || 0);
  out.delete('content-encoding');
  out.delete('content-length');

  const location = out.get('location');
  if (location) out.set('location', proxUrl(location, target));
  const refresh = out.get('refresh');
  if (refresh) out.set('refresh', rewriteRefresh(refresh, target));

  const cookies = resp.headers.getSetCookie ? resp.headers.getSetCookie() : [];
  out.delete('set-cookie');
  for (const c of cookies) out.append('set-cookie', rewriteCookie(c));

  const init = { status: resp.status, statusText: resp.statusText, headers: out };
  if (request.method === 'HEAD' || [204, 205, 304].includes(resp.status) || !resp.body) {
    return new Response(null, init);
  }

  const type = (out.get('content-type') || '').toLowerCase();
  if (length > MAX_BUFFERED_BYTES) return new Response(resp.body, init);

  if (/text\/html|application\/xhtml\+xml/.test(type)) {
    const html = decodeHtml(new Uint8Array(await resp.arrayBuffer()), type);
    out.set('content-type', `${type.split(';')[0].trim()}; charset=utf-8`);
    out.set('referrer-policy', 'same-origin');
    out.set('cache-control', 'no-store');
    return new Response(rewriteHtml(html, target), init);
  }
  if (type.includes('text/css')) {
    return new Response(rewriteCss(await resp.text(), target), init);
  }
  const dest = request.headers.get('sec-fetch-dest') || '';
  if (/javascript|ecmascript/.test(type) || (type.includes('text/plain') && /^(?:script|worker|sharedworker)$/.test(dest))) {
    out.set('x-px-js', '1');
    return new Response(rewriteJs(await resp.text(), target.href, vmCheck), init);
  }
  return new Response(resp.body, init);
}

// Cookies land on the worker's origin; make them usable inside a cross-site iframe.
function rewriteCookie(cookie) {
  const parts = cookie.split(';').map((p) => p.trim()).filter(Boolean);
  const kept = [parts[0]];
  for (const attr of parts.slice(1)) {
    const name = attr.split('=')[0].toLowerCase();
    if (['domain', 'samesite', 'secure', 'partitioned'].includes(name)) continue;
    kept.push(attr);
  }
  kept.push('SameSite=None', 'Secure', 'Partitioned');
  return kept.join('; ');
}

// ---------------------------------------------------------------- HTML

// Pages are re-served as UTF-8, so decode them using their declared charset.
function decodeHtml(bytes, contentType) {
  let charset = (/charset=["']?([\w-]+)/i.exec(contentType) || [])[1];
  if (!charset) {
    const head = new TextDecoder('latin1').decode(bytes.subarray(0, 4096));
    charset = (/<meta[^>]+charset=["']?([\w-]+)/i.exec(head) || [])[1];
  }
  try {
    return new TextDecoder(charset || 'utf-8').decode(bytes);
  } catch {
    return new TextDecoder().decode(bytes);
  }
}

const URL_ATTRS = ['src', 'action', 'formaction', 'poster', 'background'];

function rewriteHtml(html, upstream) {
  const script = runtimeScript(upstream.href, PREFIX, false);
  const ctx = { base: upstream };
  let injected = false;

  const out = transformHtml(html, {
    tag(t) {
      const name = t.name;
      if (!injected && (name === 'html' || name === 'head' || name === 'body')) {
        injected = true;
        t.append(script);
      }

      for (const a of URL_ATTRS) {
        const v = t.get(a);
        if (v != null) t.set(a, proxUrl(v, ctx.base));
      }
      const srcset = t.get('srcset');
      if (srcset != null) t.set('srcset', proxSrcset(srcset, ctx.base));
      const style = t.get('style');
      if (style != null) t.set('style', rewriteCss(style, ctx.base));
      t.removeAttr('integrity');
      for (const a of t.attrs) {
        if (/^on/i.test(a.name)) t.set(a.name, rewriteJs(a.value));
      }

      const href = t.get('href');
      switch (name) {
        case 'base':
          if (href == null) break;
          try { ctx.base = new URL(href, upstream); } catch { break; }
          t.set('href', proxLink(ctx.base.href, upstream, upstream));
          break;
        case 'a':
        case 'area':
          if (href != null) t.set('href', /^\s*javascript:/i.test(href) ? jsHref(href) : proxLink(href, ctx.base, upstream));
          t.removeAttr('ping');
          break;
        case 'link':
        case 'use':
        case 'image':
          if (href != null) t.set('href', proxUrl(href, ctx.base));
          break;
        case 'object': {
          const data = t.get('data');
          if (data != null) t.set('data', proxUrl(data, ctx.base));
          break;
        }
        case 'meta': {
          const eq = (t.get('http-equiv') || '').toLowerCase();
          if ((t.get('name') || '').toLowerCase() === 'referrer') t.remove();
          else if (eq.startsWith('content-security-policy') || eq === 'x-frame-options') t.remove();
          else if (eq === 'refresh') t.set('content', rewriteRefresh(t.get('content') || '', ctx.base));
          else if (eq === 'content-type') t.set('content', 'text/html; charset=utf-8');
          if (t.get('charset') != null) t.set('charset', 'utf-8');
          break;
        }
      }
    },
    rawText(t, text) {
      if (t.name === 'style') return rewriteCss(text, ctx.base);
      if (t.name === 'script' && (t.get('type') || '').trim().toLowerCase() === 'importmap') {
        return rewriteImportMap(text, ctx.base);
      }
      if (t.name === 'script' && isJsType(t.get('type'))) return rewriteJs(text, ctx.base.href, vmCheck);
      return text;
    },
  });

  if (injected) return out;
  // No <html>/<head>/<body> tag: put the runtime first, after any doctype.
  return out.replace(/^(\s*<!doctype[^>]*>)?/i, (m) => m + script);
}

// javascript: URLs keep their code, rewritten like any other script.
function jsHref(href) {
  const i = href.indexOf(':') + 1;
  return href.slice(0, i) + rewriteJs(href.slice(i));
}

// Node can tell us whether rewritten code still compiles (modules excepted).
function vmCheck(code) {
  try { new vm.Script(code); return true; } catch { return false; }
}

function rewriteImportMap(json, base) {
  try {
    const map = JSON.parse(json);
    const fix = (obj) => {
      for (const k of Object.keys(obj || {})) {
        if (typeof obj[k] === 'string') obj[k] = proxUrl(obj[k], base);
      }
    };
    fix(map.imports);
    for (const scope of Object.values(map.scopes || {})) fix(scope);
    return JSON.stringify(map);
  } catch {
    return json;
  }
}

// ---------------------------------------------------------------- pages

const PAGE_STYLE = `
  :root{color-scheme:light dark;--bg:#f7f7f5;--fg:#1d1d1b;--mute:#6b6b66;--card:#fff;--line:#e4e4df}
  @media (prefers-color-scheme:dark){:root{--bg:#141413;--fg:#ececea;--mute:#9a9a94;--card:#1e1e1c;--line:#2e2e2b}}
  body{margin:0;min-height:100vh;display:grid;place-items:center;background:var(--bg);color:var(--fg);font:15px/1.5 system-ui,sans-serif;padding:16px;box-sizing:border-box}
  .c{max-width:560px;width:100%;background:var(--card);border:1px solid var(--line);border-radius:12px;padding:24px}
  .s{color:var(--mute);font-size:13px;letter-spacing:.04em;text-transform:uppercase}
  h1{margin:4px 0 12px;font-size:20px}
  pre,code{white-space:pre-wrap;word-break:break-all;font-size:13px}
  pre{color:var(--mute);margin:0}`;

const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]);

function page(status, html) {
  return new Response(`<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><style>${PAGE_STYLE}</style>${html}`, {
    status,
    headers: { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-store' },
  });
}

function errorPage(status, title, detail) {
  return page(status, `<title>${esc(title)}</title><div class="c"><div class="s">Error ${status}</div><h1>${esc(title)}</h1><pre>${esc(detail)}</pre></div>`);
}

function usagePage(self) {
  const example = `${self.origin}${PREFIX}https://example.com/`;
  return page(self.pathname === '/' ? 200 : 404, `<title>Peekaboom</title><div class="c"><div class="s">Peekaboom</div><h1>Embed a site</h1>
<pre>&lt;iframe src="${esc(example)}"&gt;&lt;/iframe&gt;</pre></div>`);
}

// ---------------------------------------------------------------- HTML tokenizer

// Small HTML rewriter. It walks the document once, hands every
// start tag to `tag(t)` so attributes can be read and changed, and hands the
// contents of raw-text elements (<script>, <style>, ...) to `rawText(t, text)`.
// Everything it doesn't touch is copied through byte for byte.

const RAW_TEXT = new Set(['script', 'style', 'textarea', 'title', 'xmp', 'iframe', 'noembed', 'noframes', 'noscript']);
const SPACE = new Set([' ', '\t', '\n', '\r', '\f']);

function transformHtml(html, { tag: onTag, rawText: onRawText }) {
  const out = [];
  const n = html.length;
  let i = 0;
  while (i < n) {
    const lt = html.indexOf('<', i);
    if (lt === -1) { out.push(html.slice(i)); break; }
    out.push(html.slice(i, lt));
    const c = html[lt + 1] || '';

    // Comments, doctype, processing instructions and end tags pass through.
    if (html.startsWith('<!--', lt)) {
      i = skipTo(html, '-->', lt + 4);
      out.push(html.slice(lt, i));
      continue;
    }
    if (c === '!' || c === '?' || c === '/') {
      i = skipTo(html, '>', lt + 1);
      out.push(html.slice(lt, i));
      continue;
    }
    if (!/[a-zA-Z]/.test(c)) { out.push('<'); i = lt + 1; continue; }

    const t = parseTag(html, lt);
    if (!t) { out.push(html.slice(lt)); break; } // unterminated tag at EOF
    i = t.end;
    onTag(t);
    out.push(t.toString(), t.appended);

    if (RAW_TEXT.has(t.name)) {
      const close = new RegExp(`</${t.name}[\\s/>]`, 'ig');
      close.lastIndex = i;
      const m = close.exec(html);
      const end = m ? m.index : n;
      const text = html.slice(i, end);
      out.push(onRawText ? onRawText(t, text) ?? text : text);
      i = end;
    }
  }
  return out.join('');
}

function skipTo(s, needle, from) {
  const e = s.indexOf(needle, from);
  return e === -1 ? s.length : e + needle.length;
}

function parseTag(s, start) {
  const n = s.length;
  let i = start + 1;
  while (i < n && !SPACE.has(s[i]) && s[i] !== '/' && s[i] !== '>') i++;
  const rawName = s.slice(start + 1, i);
  const attrs = [];
  while (i < n) {
    while (i < n && (SPACE.has(s[i]) || s[i] === '/')) i++;
    if (i >= n) return null;
    if (s[i] === '>') {
      return new Tag(rawName, attrs, s[i - 1] === '/', s.slice(start, i + 1), i + 1);
    }
    const nameStart = i;
    i++; // the first character always belongs to the name (even "=")
    while (i < n && !SPACE.has(s[i]) && !'/>='.includes(s[i])) i++;
    const name = s.slice(nameStart, i);
    let value = null;
    let p = i;
    while (p < n && SPACE.has(s[p])) p++;
    if (s[p] === '=') {
      p++;
      while (p < n && SPACE.has(s[p])) p++;
      const q = s[p];
      if (q === '"' || q === "'") {
        const e = s.indexOf(q, p + 1);
        if (e === -1) return null;
        value = s.slice(p + 1, e);
        i = e + 1;
      } else {
        let e = p;
        while (e < n && !SPACE.has(s[e]) && s[e] !== '>') e++;
        value = s.slice(p, e);
        i = e;
      }
    }
    attrs.push({
      name: name.toLowerCase(),
      rawName: name,
      value: value == null ? null : decodeEntities(value),
      text: s.slice(nameStart, i),
    });
  }
  return null;
}

class Tag {
  constructor(rawName, attrs, selfClosing, raw, end) {
    this.name = rawName.toLowerCase();
    this.rawName = rawName;
    this.attrs = attrs;
    this.selfClosing = selfClosing;
    this.raw = raw;
    this.end = end;
    this.dirty = false;
    this.removed = false;
    this.appended = '';
  }

  get(name) {
    const a = this.attrs.find((x) => x.name === name);
    return a ? a.value ?? '' : null;
  }

  set(name, value) {
    const a = this.attrs.find((x) => x.name === name);
    if (a) {
      if (a.value === value) return;
      a.value = value;
      a.text = null;
    } else {
      this.attrs.push({ name, rawName: name, value, text: null });
    }
    this.dirty = true;
  }

  removeAttr(name) {
    const before = this.attrs.length;
    this.attrs = this.attrs.filter((x) => x.name !== name);
    if (this.attrs.length !== before) this.dirty = true;
  }

  remove() { this.removed = true; }

  // Insert HTML right after this start tag.
  append(html) { this.appended += html; }

  toString() {
    if (this.removed) return '';
    if (!this.dirty) return this.raw;
    const parts = this.attrs.map((a) => a.text ?? `${a.rawName}="${escapeAttr(a.value ?? '')}"`);
    return `<${this.rawName}${parts.length ? ' ' + parts.join(' ') : ''}${this.selfClosing ? ' /' : ''}>`;
  }
}

const NAMED = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: ' ' };

function decodeEntities(s) {
  if (!s.includes('&')) return s;
  return s.replace(/&(#x[0-9a-f]+|#\d+|[a-z]+)(;?)(?=(.?))/gi, (m, e, semi, next) => {
    // In attributes, "&lt=" or "&ampx" without a semicolon is left as written.
    if (!semi && /[=a-z0-9]/i.test(next)) return m;
    if (e[0] === '#') {
      const code = e[1] === 'x' || e[1] === 'X' ? parseInt(e.slice(2), 16) : parseInt(e.slice(1), 10);
      try { return String.fromCodePoint(code); } catch { return m; }
    }
    return NAMED[e.toLowerCase()] ?? m;
  });
}

function escapeAttr(s) {
  return String(s).replace(/&/g, '&amp;').replace(/"/g, '&quot;');
}

// ---------------------------------------------------------------- JavaScript rewriting

// Rewrites a script so it sees the site's own address instead of the proxy's:
// `location`, `window.location`, `document.location`, `top` and `parent` go
// through stand-ins the page runtime provides, eval() and import() arguments
// are rewritten / proxied at run time, and absolute static import specifiers
// point at the proxy. It tokenizes (strings, templates, regexes, comments)
// rather than fully parsing, so it is fast but heuristic; `check(code)`, when
// given, rejects output that no longer compiles. It never throws: on anything
// unexpected the original code is returned. Self-contained so it can be
// stringified into the page runtime and the service worker.
function rewriteJs(code, base, check) {
  const MARK = '/*__px*/';
  if (typeof code !== 'string') return code;
  const hb = /^#![^\n]*\n?/.exec(code);
  const head = hb ? hb[0] : '';
  const src = code.slice(head.length);
  if (src.startsWith(MARK)) return code;
  if (!/\b(?:location|eval|import|export|top|parent)\b/.test(src)) return code;

  try {
    const out = head + MARK + rewrite(src);
    if (check && !check(out) && check(code)) return code;
    return out;
  } catch (e) {
    return code;
  }

  function rewrite(src) {
    const toks = tokenize(src);
    const edits = [];
    const declared = (name) => new RegExp(
      `\\b(?:var|let|const|function|class)\\s+${name}\\b|(?:[(,]|(?<!\\$)\\{)\\s*${name}\\s*(?:[,)}]|=(?!=))|\\b${name}\\s*=>|\\.\\.\\.\\s*${name}\\b`,
    ).test(src);
    const skip = { location: declared('location'), top: declared('top'), parent: declared('parent') };
    const fake = (n) => (n === 'location' ? '(globalThis.__px$L||location)' : `(globalThis.__px$${n}||${n})`);
    const P = (t, v) => t && t.t === 'p' && t.v === v;
    const isDot = (t) => t && t.t === 'p' && (t.v === '.' || t.v === '?.');
    const isAssign = (t) => t && t.t === 'p' && /^(?:[-+*/%&|^]|\*\*|<<|>>>?|&&|\|\||\?\?)?=$/.test(t.v);
    const WIN = new Set(['window', 'self', 'globalThis', 'document', 'top', 'parent']);

    const stack = []; // open brackets: { cls, ev: [edit indexes] | null }
    let pendingClass = false;
    const inClass = () => stack.length > 0 && stack[stack.length - 1].cls;
    // A bare name in a class body right after `{ } ;`, a value or a modifier is a member name.
    const classMember = (p) => inClass() && (!p || p.t !== 'p' || ['{', '}', ';', ')', ']', '*'].includes(p.v));
    const objectKey = (p, nx) => (P(p, '{') || P(p, ',')) && (P(nx, ':') || P(nx, '('));

    for (let k = 0; k < toks.length; k++) {
      const t = toks[k];
      const p = toks[k - 1];
      const nx = toks[k + 1];

      if (t.t === 'q') {
        if (t.cont) stack.pop();
        if (t.open) stack.push({ cls: false, ev: null });
        continue;
      }
      if (t.t === 'p') {
        if (t.v === '{') { stack.push({ cls: pendingClass, ev: null }); pendingClass = false; }
        else if (t.v === '(' || t.v === '[') stack.push({ cls: false, ev: t.ev || null, close: t.close });
        else if (t.v === '}' || t.v === ')' || t.v === ']') {
          const f = stack.pop();
          if (f && f.ev) {
            // `eval(x) {` / `import(x) {` was a method definition, not a call.
            if (P(toks[k + 1], '{')) for (const i of f.ev) edits[i] = null;
            else edits.push([t.s, t.s, f.close]);
          }
        } else if (t.v === ',') {
          const f = stack[stack.length - 1];
          if (f && f.ev && !f.closed) { f.ev.push(edits.length); edits.push([t.s, t.s, f.close]); f.close = ''; f.closed = true; }
        }
        continue;
      }
      if (t.t !== 'i' || isDot(p)) continue;

      if (t.v === 'class' && !objectKey(p, nx)) { pendingClass = true; continue; }

      // eval(x) -> eval(__px$js(x)), import(x) -> import(__px$u(x, base))
      if ((t.v === 'eval' || t.v === 'import') && P(nx, '(') && !classMember(p)) {
        const fn = t.v === 'eval' ? '__px$js' : '__px$u';
        nx.ev = [edits.length];
        edits.push([nx.e, nx.e, `(globalThis.${fn}||(x=>x))(`]);
        nx.close = t.v === 'import' && base ? `,${JSON.stringify(base)})` : ')';
        continue;
      }
      // Static imports: import "x" / ... from "x"
      if ((t.v === 'import' || t.v === 'from') && nx && nx.t === 's') {
        const spec = nx.v.slice(1, -1);
        if (/^(?:https?:)?\/\//i.test(spec) || (base && spec[0] === '/')) {
          try {
            const abs = new URL(spec, base || 'https://invalid/');
            if (/^https?:$/.test(abs.protocol)) edits.push([nx.s, nx.e, JSON.stringify('/__px/' + abs.href)]);
          } catch (e) {}
        }
        continue;
      }

      // window.location / document.location / window.top / top.location ...
      if (WIN.has(t.v) && P(nx, '.') && toks[k + 2] && toks[k + 2].t === 'i' && !classMember(p) && !objectKey(p, nx)) {
        let obj = (t.v === 'top' || t.v === 'parent') && !skip[t.v] ? fake(t.v) : t.v;
        let j = k;
        let changed = false;
        if (t.v !== 'document' && (toks[j + 2].v === 'top' || toks[j + 2].v === 'parent') && !isAssign(toks[j + 3])) {
          const n = toks[j + 2].v;
          obj = `(${obj}.__px$${n}||${obj}.${n})`;
          j += 2;
          changed = true;
        }
        if (P(toks[j + 1], '.') && toks[j + 2] && toks[j + 2].t === 'i' && toks[j + 2].v === 'location') {
          obj = `(${obj}.__px$L||${obj}.location)` + (isAssign(toks[j + 3]) ? '.href' : '');
          j += 2;
          changed = true;
        }
        if (changed) {
          edits.push([t.s, toks[j].e, obj]);
          k = j;
          continue;
        }
      }

      // Bare location / top / parent.
      if ((t.v === 'location' || t.v === 'top' || t.v === 'parent') && !skip[t.v]) {
        if (objectKey(p, nx) || classMember(p) || P(nx, '(') || P(nx, '=>')) continue;
        if (p && p.t === 'i' && /^(?:var|let|const|function|class|get|set|static|async|typeof)$/.test(p.v) &&
          !(t.v === 'location' && p.v === 'typeof')) continue;
        if (t.v === 'location') {
          edits.push([t.s, t.e, fake('location') + (isAssign(nx) ? '.href' : '')]);
        } else if (!isAssign(nx) && !P(nx, '++') && !P(nx, '--')) {
          edits.push([t.s, t.e, fake(t.v)]);
        }
      }
    }

    let out = '';
    let pos = 0;
    for (const e of edits.filter(Boolean).sort((a, b) => a[0] - b[0])) {
      out += src.slice(pos, e[0]) + e[2];
      pos = e[1];
    }
    return out + src.slice(pos);
  }

  // Significant tokens: i(dent), p(unct), s(tring), n(umber), r(egex), q (template chunk).
  function tokenize(src) {
    const n = src.length;
    const toks = [];
    const parens = [];
    const braces = [];
    const KW = new Set(['return', 'typeof', 'instanceof', 'in', 'of', 'new', 'delete', 'void', 'throw',
      'case', 'do', 'else', 'yield', 'await', 'extends']);
    const CTL = new Set(['if', 'while', 'for', 'with']);
    const IDC = '\\w$\\u0080-\\u009f\\u00a1-\\u167f\\u1681-\\u1fff\\u200c\\u200d\\u2030-\\u205e\\u2060-\\u2fff\\u3001-\\ufefe\\uff00-\\uffff\\\\';
    const IDENT = new RegExp(`#?[${IDC.replace('\\w', 'A-Za-z_')}][${IDC}]*`, 'y');
    const NUM = /(?:0[xXbBoO][\da-fA-F_]+|(?:\d[\d_]*\.?[\d_]*|\.\d[\d_]*)(?:[eE][+-]?[\d_]+)?)n?/y;
    const PUNCT = /\.\.\.|>>>=?|===|!==|\*\*=|<<=|>>=|&&=|\|\|=|\?\?=|=>|==|!=|<=|>=|&&|\|\||\?\?|\?\.(?!\d)|\+\+|--|[-+*/%&|^]=|\*\*|<<|>>|[{}()[\];,<>+\-*/%&|^!~?:=.@#]/y;
    let prev = null;
    const push = (t) => { toks.push(t); prev = t; };
    const regexOk = () => {
      if (!prev) return true;
      switch (prev.t) {
        case 'n': case 's': case 'r': return false;
        case 'q': return prev.open;
        case 'i': return KW.has(prev.v);
        default:
          if (prev.v === ')') return prev.ctl;
          return !(prev.v === ']' || prev.v === '++' || prev.v === '--');
      }
    };
    const tpl = (s, cont) => {
      let j = s;
      while (j < n) {
        const c = src[j];
        if (c === '\\') j += 2;
        else if (c === '`') { push({ t: 'q', s: s - 1, e: j + 1, open: false, cont }); return j + 1; }
        else if (c === '$' && src[j + 1] === '{') {
          braces.push('t');
          push({ t: 'q', s: s - 1, e: j + 2, open: true, cont });
          return j + 2;
        } else j++;
      }
      push({ t: 'q', s: s - 1, e: n, open: false, cont });
      return n;
    };

    let i = 0;
    while (i < n) {
      const c = src.charCodeAt(i);
      if (c === 32 || c === 10 || c === 9 || c === 13 || c === 11 || c === 12 ||
        (c > 127 && /\s/.test(src[i]))) { i++; continue; }
      const ch = src[i];
      if (ch === '/') {
        const d = src[i + 1];
        if (d === '/') { const e = src.indexOf('\n', i); i = e < 0 ? n : e; continue; }
        if (d === '*') { const e = src.indexOf('*/', i + 2); i = e < 0 ? n : e + 2; continue; }
        if (regexOk()) {
          let j = i + 1;
          let cls = false;
          for (; j < n; j++) {
            const x = src[j];
            if (x === '\\') j++;
            else if (x === '\n') { j = -1; break; }
            else if (x === '[') cls = true;
            else if (x === ']') cls = false;
            else if (x === '/' && !cls) break;
          }
          if (j > 0 && j < n) {
            j++;
            while (j < n && /[a-z]/i.test(src[j])) j++;
            push({ t: 'r', s: i, e: j });
            i = j;
            continue;
          }
        }
      }
      if (ch === '"' || ch === "'") {
        let j = i + 1;
        for (; j < n; j++) {
          const x = src[j];
          if (x === '\\') j++;
          else if (x === ch || x === '\n') break;
        }
        j = Math.min(j + 1, n);
        push({ t: 's', s: i, e: j, v: src.slice(i, j) });
        i = j;
        continue;
      }
      if (ch === '`') { i = tpl(i + 1, false); continue; }
      if (ch === '}' && braces[braces.length - 1] === 't') { braces.pop(); i = tpl(i + 1, true); continue; }

      IDENT.lastIndex = i;
      let m = IDENT.exec(src);
      if (m) { push({ t: 'i', s: i, e: i + m[0].length, v: m[0] }); i += m[0].length; continue; }
      if ((c >= 48 && c <= 57) || (ch === '.' && /\d/.test(src[i + 1] || ''))) {
        NUM.lastIndex = i;
        m = NUM.exec(src);
        const e = i + (m ? m[0].length || 1 : 1);
        push({ t: 'n', s: i, e });
        i = e;
        continue;
      }
      PUNCT.lastIndex = i;
      m = PUNCT.exec(src);
      const v = m ? m[0] : ch;
      const tok = { t: 'p', s: i, e: i + v.length, v };
      if (v === '{') braces.push('b');
      else if (v === '}') braces.pop();
      else if (v === '(') parens.push(!!(prev && prev.t === 'i' && CTL.has(prev.v)));
      else if (v === ')') tok.ctl = !!parens.pop();
      push(tok);
      i += v.length;
    }
    return toks;
  }
}

function isJsType(type) {
  const t = (type || '').trim().toLowerCase().split(';')[0];
  return t === '' || t === 'module' || /^(?:text|application)\/(?:x-)?(?:javascript|ecmascript|jscript|livescript)/.test(t);
}

// ---------------------------------------------------------------- service worker

// Served at /__px_sw.js and registered by the page runtime. It catches the
// requests the runtime's patches miss (CSS fonts, innerHTML images, worker
// imports, ...): cross-origin ones go through /__px/, unprefixed same-origin
// ones are mapped to the site of the page that made them, and scripts the
// server did not rewrite (no x-px-js header) are run through rewriteJs.
function serviceWorker(PREFIX, rewriteJs) {
  const ME = self.location.origin;
  const origins = new Map(); // clientId -> upstream origin of an outermost frame

  self.addEventListener('install', () => self.skipWaiting());
  self.addEventListener('activate', (e) => e.waitUntil(Promise.all([
    self.clients.claim(),
    // Drop caches made by an older rewriter.
    cacheName.then((name) => caches.keys().then((keys) => Promise.all(
      keys.filter((k) => k.startsWith('__px-js-') && k !== name).map((k) => caches.delete(k))))),
  ])));
  self.addEventListener('message', (e) => {
    const d = e.data;
    if (d && d.__px === 'origin' && e.source && e.source.id) origins.set(e.source.id, d.origin);
  });
  self.addEventListener('fetch', (e) => {
    const req = e.request;
    if (req.mode === 'navigate' || !/^https?:/.test(req.url)) return;
    const url = new URL(req.url);
    if (url.origin === ME) {
      if (url.pathname === '/__px_sw.js' || (url.pathname === '/' && url.searchParams.has('url'))) return;
      if (url.pathname.startsWith(PREFIX)) {
        if (isScript(req)) e.respondWith(fetch(req).then((r) => rewriteResponse(r, url.href.slice(ME.length + PREFIX.length))));
        return;
      }
      e.respondWith(siteOf(e.clientId).then((origin) =>
        origin ? forward(req, origin + url.pathname + url.search) : fetch(req)));
      return;
    }
    e.respondWith(forward(req, url.href));
  });

  function isScript(req) {
    return ['script', 'worker', 'sharedworker', 'serviceworker'].includes(req.destination);
  }

  async function siteOf(clientId) {
    if (!clientId) return null;
    if (origins.has(clientId)) return origins.get(clientId);
    const c = await self.clients.get(clientId);
    if (!c || !c.url.startsWith(ME + PREFIX)) return null;
    try { return new URL(c.url.slice(ME.length + PREFIX.length)).origin; } catch (err) { return null; }
  }

  async function forward(req, upstream) {
    const init = {
      method: req.method,
      headers: req.headers,
      credentials: 'include',
      cache: req.cache === 'only-if-cached' ? 'default' : req.cache,
      redirect: 'follow',
      signal: req.signal,
    };
    if (!['GET', 'HEAD'].includes(req.method)) init.body = await req.arrayBuffer();
    let r;
    try {
      r = await fetch(ME + PREFIX + upstream, init);
    } catch (err) {
      return Response.error();
    }
    return isScript(req) ? rewriteResponse(r, upstream) : r;
  }

  async function rewriteResponse(r, upstream) {
    const type = (r.headers.get('content-type') || '').toLowerCase();
    if (!r.ok || r.headers.has('x-px-js') || !/javascript|ecmascript|text\/plain/.test(type)) return r;
    const src = await r.text();
    const code = await cachedRewrite(src, upstream);
    const headers = new Headers(r.headers);
    headers.delete('content-length');
    headers.set('x-px-js', '1');
    return new Response(code, { status: r.status, statusText: r.statusText, headers });
  }

  // Rewritten scripts are cached by a hash of their URL and source, so a
  // script is rewritten once per version no matter how its HTTP caching is set
  // up. The cache name carries a hash of the rewriter, so changing it starts
  // a fresh cache. Small scripts aren't worth the cache I/O.
  const CACHE_MIN = 8 * 1024;
  const CACHE_MAX_ENTRIES = 300;
  const cacheName = sha256(String(rewriteJs)).then((h) => '__px-js-' + h.slice(0, 16));
  let pruning = null;

  async function cachedRewrite(src, upstream) {
    const check = (c) => { try { new Function(c); return true; } catch (err) { return false; } };
    if (src.length < CACHE_MIN) return rewriteJs(src, upstream, check);
    let cache, key;
    try {
      cache = await caches.open(await cacheName);
      key = ME + '/__px_cache/' + (await sha256(upstream + '\n' + src));
      const hit = await cache.match(key);
      if (hit) return hit.headers.has('x-px-same') ? src : hit.text();
    } catch (err) {
      cache = null; // Cache API unavailable (e.g. private mode): just rewrite.
    }
    const code = rewriteJs(src, upstream, check);
    if (cache) {
      // Unchanged scripts store an empty marker instead of a second copy.
      const entry = code === src
        ? new Response('', { headers: { 'x-px-same': '1' } })
        : new Response(code, { headers: { 'content-type': 'application/javascript' } });
      cache.put(key, entry).then(() => prune(cache)).catch(() => {});
    }
    return code;
  }

  // Keep the cache bounded; keys() lists oldest entries first.
  function prune(cache) {
    if (pruning) return pruning;
    pruning = cache.keys().then((keys) => Promise.all(
      keys.slice(0, Math.max(0, keys.length - CACHE_MAX_ENTRIES)).map((k) => cache.delete(k)),
    )).catch(() => {}).then(() => { pruning = null; });
    return pruning;
  }

  async function sha256(s) {
    const buf = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(s));
    return Array.from(new Uint8Array(buf), (b) => b.toString(16).padStart(2, '0')).join('');
  }
}

const SW_SCRIPT = `(function(__name){(${serviceWorker})(${JSON.stringify(PREFIX)}, ${rewriteJs});})(function(f){return f;});`;

function serviceWorkerResponse() {
  return new Response(SW_SCRIPT, {
    headers: {
      'content-type': 'application/javascript; charset=utf-8',
      'cache-control': 'no-cache',
      'service-worker-allowed': '/',
    },
  });
}

// ---------------------------------------------------------------- injected page script

// Runs inside every proxied HTML page before any site script.
//
// Proxied URLs look like  <worker>/__px/https://site.com/path.  In the outermost
// proxied frame the address is immediately replaced with the site's real path
// (<worker>/path) so client-side routers see the paths they expect. Requests
// the page then makes are pointed back at /__px/... here, and anything that
// slips through is caught by the service worker, or resolved by the server
// from the Referer or __px_origin cookie. Scripts are rewritten (rewriteJs) to
// read location / top / parent through the stand-ins defined here.
function runtime(C, rewriteJs) {
  if (window.__pxRuntime) return;
  window.__pxRuntime = true;

  const ME = location.origin;
  const P = ME + C.prefix;
  const UP = new URL(C.upstream);

  let nested = false;
  try { nested = window.parent !== window && !!window.parent.__pxRuntime; } catch (e) {}

  // Upstream URL of the current document / base.
  function upHere() {
    if (location.href.startsWith(P)) return location.href.slice(P.length);
    return UP.origin + location.pathname + location.search + location.hash;
  }
  function upBase() {
    const b = document.baseURI;
    if (b.startsWith(P)) return b.slice(P.length);
    try {
      const x = new URL(b);
      if (x.origin === ME) return UP.origin + x.pathname + x.search;
    } catch (e) {}
    return upHere();
  }

  function isProxied(s) { return s.startsWith(C.prefix) || s.startsWith(P); }

  function prox(u) {
    if (u == null) return u;
    const s = String(u instanceof URL ? u.href : u).trim();
    if (!s || s[0] === '#' || isProxied(s) || /^(data|blob|javascript|about|mailto|tel|sms):/i.test(s)) return u;
    let x;
    try { x = new URL(s, upBase()); } catch (e) { return u; }
    if (x.origin === ME) x = new URL(x.pathname + x.search + x.hash, UP.origin);
    if (!/^(https?|wss?):$/.test(x.protocol)) return u;
    if (x.protocol === 'ws:' || x.protocol === 'wss:') {
      return (location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + C.prefix + x.href;
    }
    return P + x.href;
  }

  function proxSrcset(v) {
    return String(v).split(/,\s+/).map((part) => {
      const m = part.trim().match(/^(\S+)(\s+.*)?$/);
      return m ? prox(m[1]) + (m[2] || '') : part;
    }).join(', ');
  }

  // Outermost proxied frame: show the real path and remember the site.
  if (!nested) {
    if (location.href.startsWith(P)) {
      const real = new URL(upHere());
      if (real.origin === UP.origin) history.replaceState(history.state, '', real.pathname + real.search + real.hash);
    }
    try {
      document.cookie = '__px_origin=' + encodeURIComponent(UP.origin) +
        '; path=/; SameSite=None; Secure; Partitioned';
    } catch (e) {}
  }

  // Network APIs
  // Streamed request bodies need HTTP/2, which the proxy may not be served
  // over (e.g. plain Node on http://), so read them into a buffer first.
  const isStream = (b) => typeof ReadableStream !== 'undefined' && b instanceof ReadableStream;
  const _fetch = window.fetch;
  window.fetch = async function (input, init) {
    if (init && isStream(init.body)) {
      init = { ...init, body: await new Response(init.body).arrayBuffer() };
      delete init.duplex;
    }
    if (input instanceof Request) {
      const r = input;
      const p = prox(r.url);
      const hasBody = !!r.body && !(init && 'body' in init);
      if (p !== r.url || hasBody) {
        const o = {
          method: r.method, headers: r.headers, credentials: r.credentials, cache: r.cache,
          redirect: r.redirect, referrer: r.referrer, referrerPolicy: r.referrerPolicy,
          keepalive: r.keepalive, signal: r.signal,
        };
        if (r.mode !== 'navigate') o.mode = r.mode;
        if (hasBody) o.body = await r.arrayBuffer();
        input = new Request(p, o);
      }
    } else {
      input = prox(input);
    }
    return _fetch.call(this, input, init);
  };

  const _open = XMLHttpRequest.prototype.open;
  XMLHttpRequest.prototype.open = function (method, url, ...rest) {
    return _open.call(this, method, prox(url), ...rest);
  };

  for (const name of ['WebSocket', 'EventSource', 'Worker', 'SharedWorker']) {
    const Orig = window[name];
    if (!Orig) continue;
    window[name] = new Proxy(Orig, {
      construct(target, args, newTarget) {
        if (args.length) args[0] = prox(args[0]);
        return Reflect.construct(target, args, newTarget);
      },
    });
  }

  if (navigator.sendBeacon) {
    const _beacon = navigator.sendBeacon.bind(navigator);
    navigator.sendBeacon = (url, data) => _beacon(prox(url), data);
  }

  const _wopen = window.open;
  window.open = function (url, ...rest) {
    return _wopen.call(this, url == null || url === '' ? url : prox(url), ...rest);
  };

  // Our service worker catches whatever these patches miss. The site's own
  // service workers are refused, and it can't see or unregister ours.
  const sw = navigator.serviceWorker;
  if (sw) {
    try {
      sw.register('/__px_sw.js', { scope: '/' }).catch(() => {});
      const hello = () => { if (sw.controller) sw.controller.postMessage({ __px: 'origin', origin: UP.origin }); };
      hello();
      sw.addEventListener('controllerchange', () => {
        hello();
        // First visit without server-side script rewriting: reload once now that scripts can be rewritten.
        if (C.swReload && !nested && !sessionStorage.getItem('__px_sw')) {
          sessionStorage.setItem('__px_sw', '1');
          location.reload();
        }
      });
    } catch (e) {}
    try {
      sw.register = () => Promise.reject(new DOMException('Service workers are disabled by the proxy', 'SecurityError'));
      sw.getRegistrations = () => Promise.resolve([]);
      sw.getRegistration = () => Promise.resolve(undefined);
    } catch (e) {}
  }

  // Stand-ins that rewritten scripts use for location, top and parent.
  const real = location;
  function go(u, replace) {
    let x;
    try { x = new URL(String(u), upBase()); } catch (e) { return; }
    if (!/^https?:$/.test(x.protocol)) return replace ? real.replace(String(u)) : real.assign(String(u));
    const here = upHere();
    if (x.hash && x.href.split('#')[0] === here.split('#')[0]) { real.hash = x.hash; return; }
    const p = prox(x.href);
    return replace ? real.replace(p) : real.assign(p);
  }

  // Safety net for navigations the rewriter missed (e.g. an aliased
  // `w.location.href = 'https://site/...'`): cancel any that would leave the
  // proxy and send them through it instead.
  try {
    window.navigation.addEventListener('navigate', (e) => {
      if (!e.cancelable || e.formData || e.downloadRequest || e.navigationType === 'traverse') return;
      let x;
      try { x = new URL(e.destination.url); } catch (err) { return; }
      if (x.origin === ME || !/^https?:$/.test(x.protocol)) return;
      e.preventDefault();
      const p = prox(x.href);
      e.navigationType === 'replace' ? real.replace(p) : real.assign(p);
    });
  } catch (e) {}
  const L = {};
  Object.defineProperty(L, 'href', { get: upHere, set: (v) => go(v), enumerable: true });
  for (const k of ['origin', 'protocol', 'host', 'hostname', 'port', 'pathname', 'search', 'hash']) {
    Object.defineProperty(L, k, {
      get: () => new URL(upHere())[k],
      set: k === 'origin' ? undefined : (v) => {
        if (k === 'hash') { real.hash = v; return; }
        const x = new URL(upHere());
        x[k] = v;
        go(x.href);
      },
      enumerable: true,
    });
  }
  Object.defineProperty(L, 'ancestorOrigins', { get: () => real.ancestorOrigins });
  L.assign = (u) => go(u);
  L.replace = (u) => go(u, true);
  L.reload = () => real.reload();
  L.toString = upHere;
  L[Symbol.toStringTag] = 'Location';

  let pxTop = window;
  try { while (pxTop.parent !== pxTop && pxTop.parent.__pxRuntime) pxTop = pxTop.parent; } catch (e) {}
  const _F = Function;
  const jsCheck = (c) => { try { new _F(c); return true; } catch (e) { return false; } };
  const js = (s) => (typeof s === 'string' ? rewriteJs(s, upBase(), jsCheck) : s);
  const hidden = (obj, name, value) => {
    try { Object.defineProperty(obj, name, { value, configurable: true }); } catch (e) {}
  };
  hidden(window, '__px$L', L);
  hidden(document, '__px$L', L);
  hidden(window, '__px$top', pxTop);
  hidden(window, '__px$parent', nested ? window.parent : window);
  hidden(window, '__px$origin', UP.origin);
  hidden(window, '__px$js', js);
  hidden(window, '__px$u', (u, base) => {
    if (typeof u !== 'string' && !(u instanceof URL)) return u;
    try { return prox(new URL(String(u), base || upBase()).href); } catch (e) { return u; }
  });

  // Code built from strings: new Function(...), setTimeout("...").
  const FnProxy = new Proxy(_F, {
    apply: (t, self, a) => Reflect.apply(t, self, fnArgs(a)),
    construct: (t, a, nt) => Reflect.construct(t, fnArgs(a), nt === FnProxy ? t : nt),
  });
  function fnArgs(a) {
    a = Array.from(a);
    if (a.length && typeof a[a.length - 1] === 'string') a[a.length - 1] = js(a[a.length - 1]);
    return a;
  }
  try {
    window.Function = FnProxy;
    _F.prototype.constructor = FnProxy;
  } catch (e) {}
  for (const n of ['setTimeout', 'setInterval']) {
    const orig = window[n];
    window[n] = function (f, ...rest) { return orig.call(window, js(f), ...rest); };
  }

  // What the document says about its own address.
  function unprox(s) {
    if (s.startsWith(P)) return s.slice(P.length);
    if (s === ME || s.startsWith(ME + '/')) return UP.origin + s.slice(ME.length);
    return s;
  }
  const ref = document.referrer;
  const own = (obj, name, get) => {
    try { Object.defineProperty(obj, name, { get, configurable: true }); } catch (e) {}
  };
  own(document, 'URL', upHere);
  own(document, 'documentURI', upHere);
  own(document, 'referrer', () => (ref.startsWith(ME + '/') ? unprox(ref) : ''));
  own(window, 'origin', () => UP.origin);
  for (const cls of ['HTMLAnchorElement', 'HTMLAreaElement']) {
    const proto = window[cls].prototype;
    const d = Object.getOwnPropertyDescriptor(proto, 'href');
    if (!d) continue;
    Object.defineProperty(proto, 'href', { ...d, get() { return unprox(d.get.call(this)); } });
    for (const k of ['origin', 'protocol', 'host', 'hostname', 'port']) {
      const dk = Object.getOwnPropertyDescriptor(proto, k);
      if (!dk) continue;
      Object.defineProperty(proto, k, {
        ...dk,
        get() { try { return new URL(this.href)[k]; } catch (e) { return dk.get.call(this); } },
      });
    }
  }

  // postMessage between proxied frames: every frame really has the proxy's
  // origin, so target origins are mapped to it and event.origin back to the site.
  const _pm = window.postMessage;
  window.postMessage = function (msg, target, transfer) {
    if (target && typeof target === 'object') target = { ...target, targetOrigin: mapOrigin(target.targetOrigin) };
    else target = mapOrigin(target);
    return _pm.call(this || window, msg, target, transfer);
  };
  function mapOrigin(o) { return o == null || o === '*' || o === '/' ? o : ME; }
  const originDesc = Object.getOwnPropertyDescriptor(MessageEvent.prototype, 'origin');
  if (originDesc && originDesc.get) {
    Object.defineProperty(MessageEvent.prototype, 'origin', {
      ...originDesc,
      get() {
        const o = originDesc.get.call(this);
        if (o !== ME) return o;
        try { if (this.source && this.source.__px$origin) return this.source.__px$origin; } catch (e) {}
        return UP.origin;
      },
    });
  }

  try {
    Object.defineProperty(document, 'domain', { get: () => UP.hostname, set: () => {}, configurable: true });
  } catch (e) {}

  // DOM URL attributes. Links (<a>, <area>) are left alone so routers can read
  // real paths; the click handler below routes them through the proxy.
  const isLink = (el) => el instanceof HTMLAnchorElement || el instanceof HTMLAreaElement;
  const URL_ATTRS = new Set(['src', 'href', 'action', 'formaction', 'poster', 'data']);
  const _setAttr = Element.prototype.setAttribute;
  Element.prototype.setAttribute = function (name, value) {
    const n = String(name).toLowerCase();
    if (URL_ATTRS.has(n) && !isLink(this)) value = prox(value);
    else if (n === 'srcset') value = proxSrcset(value);
    else if (n === 'integrity') return;
    else if (n.startsWith('on')) value = js(String(value));
    return _setAttr.call(this, name, value);
  };

  const PROPS = [
    ['HTMLScriptElement', 'src'], ['HTMLImageElement', 'src'], ['HTMLImageElement', 'srcset', proxSrcset],
    ['HTMLSourceElement', 'src'], ['HTMLSourceElement', 'srcset', proxSrcset], ['HTMLMediaElement', 'src'],
    ['HTMLIFrameElement', 'src'], ['HTMLEmbedElement', 'src'], ['HTMLTrackElement', 'src'],
    ['HTMLLinkElement', 'href'], ['HTMLFormElement', 'action'], ['HTMLVideoElement', 'poster'],
    ['HTMLObjectElement', 'data'],
  ];
  for (const [cls, prop, fn = prox] of PROPS) {
    const proto = window[cls] && window[cls].prototype;
    const desc = proto && Object.getOwnPropertyDescriptor(proto, prop);
    if (!desc || !desc.set) continue;
    Object.defineProperty(proto, prop, { ...desc, set(v) { desc.set.call(this, fn(v)); } });
  }

  // Elements inserted via innerHTML bypass the setters above.
  const ATTRS = { src: prox, srcset: proxSrcset, poster: prox, action: prox, data: prox };
  function fixTree(root) {
    if (root.nodeType !== 1) return;
    const els = [root, ...root.querySelectorAll('[src],[srcset],[poster],[action],link[href],object[data]')];
    for (const el of els) {
      for (const a in ATTRS) {
        const v = el.getAttribute(a);
        if (v != null) {
          const nv = ATTRS[a](v);
          if (nv !== v) _setAttr.call(el, a, nv);
        }
      }
      if (el instanceof HTMLLinkElement) {
        const v = el.getAttribute('href');
        const nv = v != null && prox(v);
        if (nv && nv !== v) _setAttr.call(el, 'href', nv);
      }
      if (el.hasAttribute && el.hasAttribute('integrity')) el.removeAttribute('integrity');
    }
  }
  new MutationObserver((records) => {
    for (const r of records) for (const n of r.addedNodes) fixTree(n);
  }).observe(document, { childList: true, subtree: true });

  // Route link clicks through the proxy if no router handled them.
  addEventListener('click', (e) => {
    if (e.defaultPrevented) return;
    const a = e.target && e.target.closest && e.target.closest('a[href], area[href]');
    if (!a || a.hasAttribute('download')) return;
    const raw = a.getAttribute('href');
    if (!raw || raw[0] === '#' || isProxied(raw)) return;
    let x;
    try { x = new URL(a.href); } catch (err) { return; } // the site's URL (see the href getter above)
    if (!/^https?:$/.test(x.protocol)) return;
    const here = new URL(upHere());
    if (x.hash && x.origin === here.origin && x.pathname === here.pathname && x.search === here.search) return;
    _setAttr.call(a, 'href', prox(x.href));
  });

  // History: keep absolute upstream URLs on our origin and report navigation.
  for (const m of ['pushState', 'replaceState']) {
    const orig = history[m];
    history[m] = function (state, title, url) {
      if (url != null) {
        const s = String(url);
        if (s.startsWith(UP.origin + '/') || s === UP.origin) {
          url = nested ? prox(s) : s.slice(UP.origin.length) || '/';
        }
      }
      const r = orig.call(this, state, title, url);
      report();
      return r;
    };
  }

  function report() {
    if (nested || window.parent === window) return;
    try { window.parent.postMessage({ __px: 'nav', url: upHere(), title: document.title }, '*'); } catch (e) {}
  }
  addEventListener('popstate', report);
  addEventListener('hashchange', report);
  addEventListener('DOMContentLoaded', report);
  addEventListener('load', report);
}

function runtimeScript(upstream, prefix, swReload) {
  const json = JSON.stringify({ upstream, prefix, swReload }).replace(/</g, '\\u003c');
  // __name: guard against bundlers that wrap functions with a name helper.
  return `<script>(function(__name){(${runtime})(${json},${rewriteJs});})(function(f){return f;});</script>`;
}

// ---------------------------------------------------------------- HTTP server

function toRequest(req, withBody) {
  const proto = req.headers['x-forwarded-proto'] || (req.socket.encrypted ? 'https' : 'http');
  const host = req.headers['x-forwarded-host'] || req.headers.host || `localhost:${PORT}`;
  const headers = new Headers();
  for (const [k, v] of Object.entries(req.headers)) {
    if (Array.isArray(v)) v.forEach((x) => headers.append(k, x));
    else if (v != null) headers.set(k, v);
  }
  return new Request(`${proto}://${host}${req.url}`, {
    method: req.method,
    headers,
    body: withBody ? Readable.toWeb(req) : undefined,
    duplex: 'half',
  });
}

async function send(res, resp) {
  const headers = {};
  for (const [k, v] of resp.headers) if (k !== 'set-cookie') headers[k] = v;
  const cookies = resp.headers.getSetCookie();
  if (cookies.length) headers['set-cookie'] = cookies;
  res.writeHead(resp.status, resp.statusText || undefined, headers);
  if (!resp.body) return res.end();
  const body = Readable.fromWeb(resp.body);
  body.on('error', () => res.destroy());
  res.on('close', () => body.destroy());
  body.pipe(res);
}

const server = http.createServer(async (req, res) => {
  try {
    const request = toRequest(req, !['GET', 'HEAD'].includes(req.method));
    await send(res, await handle(request));
  } catch (err) {
    if (!res.headersSent) res.writeHead(500, { 'content-type': 'text/plain' });
    res.end(String((err && err.message) || err));
  }
});

// WebSockets: resolve the target like any request, then splice the raw
// sockets together after sending the upgrade request upstream.
server.on('upgrade', async (req, socket, head) => {
  socket.on('error', () => {});
  try {
    const request = toRequest(req, false);
    const r = await resolveTarget(request);
    if (r.response) {
      socket.end(`HTTP/1.1 ${r.response.status} ${r.response.statusText || 'Error'}\r\nConnection: close\r\n\r\n`);
      return;
    }
    const { self, target } = r;
    const secure = target.protocol === 'https:';
    const port = Number(target.port) || (secure ? 443 : 80);
    const up = secure
      ? tls.connect({ host: target.hostname, port, servername: target.hostname, ALPNProtocols: ['http/1.1'], lookup: safeLookup })
      : net.connect({ host: target.hostname, port, lookup: safeLookup });

    const lines = [`GET ${target.pathname}${target.search} HTTP/1.1`, `Host: ${target.host}`,
      'Connection: Upgrade', 'Upgrade: websocket'];
    for (const [k, v] of upstreamHeaders(request, self, target)) lines.push(`${k}: ${v}`);

    up.once(secure ? 'secureConnect' : 'connect', () => {
      up.write(lines.join('\r\n') + '\r\n\r\n');
      if (head && head.length) up.write(head);
      up.pipe(socket);
      socket.pipe(up);
    });
    up.on('error', () => socket.destroy());
    socket.on('close', () => up.destroy());
  } catch {
    socket.destroy();
  }
});

server.listen(PORT, HOST, () => {
  console.log(`Peekaboom listening on http://localhost:${PORT}`);
});
