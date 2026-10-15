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
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';

const PORT = Number(process.env.PORT) || 8787;
const HOST = process.env.HOST || '0.0.0.0';
const PREFIX = '/__px/';
const ORIGIN_COOKIE = '__px_origin';
const UPSTREAM_TIMEOUT_MS = 100_000; // time to response headers; slow origins can take 30s+
const MAX_BUFFERED_BYTES = 16 * 1024 * 1024; // HTML / CSS rewriting buffers the body

const DROP_REQUEST_HEADERS = new Set([
  'host', 'connection', 'keep-alive', 'proxy-connection', 'te', 'trailer', 'transfer-encoding',
  'accept-encoding', 'origin', 'referer', 'cookie', 'cdn-loop', 'x-real-ip', 'x-forwarded-for',
  'x-forwarded-proto', 'x-forwarded-host', 'true-client-ip', 'upgrade', 'expect', 'forwarded', 'via',
  'x-client-ip', 'x-forwarded-port', 'x-forwarded-scheme', 'x-px-dest',
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

// Many servers send an incomplete certificate chain. Browsers fill the gap by
// downloading the missing intermediates (named in the certificate's AIA
// extension); Node doesn't, so do the same and keep an agent per host that
// trusts them.
const hostAgents = new Map(); // host:port -> Promise<https.Agent | null>
const CHAIN_ERRORS = new Set(['UNABLE_TO_VERIFY_LEAF_SIGNATURE', 'UNABLE_TO_GET_ISSUER_CERT_LOCALLY', 'UNABLE_TO_GET_ISSUER_CERT']);
const rootCAs = () => (tls.getCACertificates ? tls.getCACertificates('default') : tls.rootCertificates);

function chainAgent(host, port) {
  const key = `${host}:${port}`;
  if (!hostAgents.has(key)) {
    const p = fetchIntermediates(host, port).then((pems) => (pems.length
      ? new https.Agent({ ...agentOpts, ca: [...rootCAs(), ...pems] })
      : null)).catch(() => null);
    hostAgents.set(key, p);
    if (hostAgents.size > 1000) hostAgents.delete(hostAgents.keys().next().value);
  }
  return hostAgents.get(key);
}

async function fetchIntermediates(host, port) {
  let cert = await new Promise((resolve, reject) => {
    const s = tls.connect({ host, port, servername: host, rejectUnauthorized: false, lookup: safeLookup });
    s.setTimeout(10_000, () => s.destroy(new Error('timeout')));
    s.once('secureConnect', () => { resolve(s.getPeerX509Certificate()); s.destroy(); });
    s.once('error', reject);
  });
  const pems = [];
  for (let depth = 0; cert && depth < 4; depth++) {
    const uri = /CA Issuers - URI:(http:\/\/\S+)/.exec(cert.infoAccess || '');
    if (!uri) break;
    const der = await download(uri[1]);
    try { cert = new crypto.X509Certificate(der); } catch { break; }
    pems.push(cert.toString());
    if (cert.issuer === cert.subject) break;
  }
  return pems;
}

function download(url) {
  return new Promise((resolve, reject) => {
    const req = http.get(url, { agent: agents['http:'], timeout: 10_000 }, (res) => {
      const chunks = [];
      let size = 0;
      res.on('data', (c) => {
        size += c.length;
        if (size > 64 * 1024) req.destroy(new Error('too large'));
        else chunks.push(c);
      });
      res.on('end', () => resolve(Buffer.concat(chunks)));
      res.on('error', reject);
    });
    req.on('timeout', () => req.destroy(new Error('timeout')));
    req.on('error', reject);
  });
}

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
async function nodeFetch(url, init = {}) {
  const u = new URL(url);
  const port = Number(u.port) || 443;
  let agent = agents[u.protocol];
  if (u.protocol === 'https:' && hostAgents.has(`${u.hostname}:${port}`)) {
    agent = (await chainAgent(u.hostname, port)) || agent;
  }
  try {
    return await nodeRequest(u, init, agent);
  } catch (err) {
    // A streamed body can't be replayed; the next request to the host will use the fixed agent.
    if (agent !== agents['https:'] || !CHAIN_ERRORS.has(err.code) || init.body) throw err;
    const fixed = await chainAgent(u.hostname, port);
    if (!fixed) throw err;
    return nodeRequest(u, init, fixed);
  }
}

function nodeRequest(u, init, agent) {
  return new Promise((resolve, reject) => {
    const headers = {};
    for (const [k, v] of new Headers(init.headers)) headers[k] = v;
    headers['accept-encoding'] = ENCODINGS.join(', ');

    const req = (u.protocol === 'https:' ? https : http).request(u, {
      method: init.method || 'GET',
      headers,
      agent,
      signal: init.signal,
      // Browsers accept large and slightly malformed responses; so should we.
      insecureHTTPParser: true,
      maxHeaderSize: 256 * 1024,
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
        out.delete('content-length');
      }
      if (noBody) res.resume();
      // Response only allows 200-599 (some sites use e.g. 999) and a plain reason phrase.
      const status = res.statusCode < 200 || res.statusCode > 599 ? 502 : res.statusCode;
      const statusText = (res.statusMessage || '').replace(/[^\t\x20-\x7e\x80-\xff]/g, '');
      resolve(new Response(noBody ? null : Readable.toWeb(body), { status, statusText, headers: out }));
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
  const cookie = siteCookies(request.headers.get('cookie'), cookieSite(target.hostname));
  if (cookie) headers.set('cookie', cookie);

  const refUp = refererUpstream(request, self);
  if (refUp) headers.set('referer', refUp.href);
  if (request.headers.has('origin')) headers.set('origin', refUp ? refUp.origin : target.origin);

  // Describe the request as the site would see it loaded directly: frames
  // become top-level documents and sec-fetch-site compares the real sites.
  if (/^i?frame$/.test(headers.get('sec-fetch-dest') || '')) headers.set('sec-fetch-dest', 'document');
  if (headers.has('sec-fetch-site')) {
    let site = headers.get('sec-fetch-site');
    if (refUp) {
      site = refUp.origin === target.origin ? 'same-origin'
        : refUp.protocol === target.protocol && cookieSite(refUp.hostname) === cookieSite(target.hostname) ? 'same-site'
          : 'cross-site';
    } else if (headers.get('sec-fetch-mode') === 'navigate') {
      site = 'none';
    }
    headers.set('sec-fetch-site', site);
  }
  return headers;
}

// The upstream page a request came from. The outermost frame shows the site's
// real path on the proxy's origin, so a plain same-origin Referer is mapped
// back using the origin cookie.
function refererUpstream(request, self) {
  const ref = request.headers.get('referer');
  if (!ref) return null;
  const up = upstreamFromProxied(ref, self);
  if (up) return up;
  try {
    const r = new URL(ref);
    const origin = r.origin === self.origin && originFromCookie(request);
    return origin ? new URL(r.pathname + r.search, origin) : null;
  } catch {
    return null;
  }
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
  return mapSrcset(value, (u) => proxUrl(u, base));
}

// Applies fn to each URL in a srcset. URLs may contain commas
// ("w_100,h_100/a.jpg 1x") and candidates needn't be followed by a space
// ("a.jpg 1x,b.jpg 2x"), so this follows the HTML parsing rules. Self-contained
// so it can be stringified into the page runtime.
function mapSrcset(value, fn) {
  const s = String(value);
  const out = [];
  let i = 0;
  while (i < s.length) {
    while (i < s.length && /[\s,]/.test(s[i])) i++;
    if (i >= s.length) break;
    let j = i;
    while (j < s.length && !/\s/.test(s[j])) j++;
    let url = s.slice(i, j);
    let desc = '';
    if (/,$/.test(url)) {
      url = url.replace(/,+$/, '');
    } else {
      let k = j;
      let depth = 0;
      for (; k < s.length; k++) {
        if (s[k] === '(') depth++;
        else if (s[k] === ')') depth--;
        else if (s[k] === ',' && depth <= 0) break;
      }
      desc = s.slice(j, k).trim();
      j = k + 1;
    }
    out.push(fn(url) + (desc ? ' ' + desc : ''));
    i = j;
  }
  return out.join(', ');
}

// `map` lets the page runtime reuse this with its own URL mapper.
function rewriteCss(css, base, map = (u) => proxUrl(u, base)) {
  return css
    .replace(/url\(\s*(?:"([^"]*)"|'([^']*)'|([^"'\s)][^)]*?))\s*\)/gi, (m, dq, sq, bare) => {
      const q = dq != null ? '"' : sq != null ? "'" : '';
      return `url(${q}${map(dq ?? sq ?? bare)}${q})`;
    })
    .replace(/@import\s+(['"])([^'"]+)\1/gi, (m, q, u) => `@import ${q}${map(u)}${q}`)
    // image-set() also takes bare strings: image-set("a.png" 1x, "b.png" 2x)
    .replace(/((?:-webkit-)?image-set\()((?:[^()]|\([^()]*\))*)\)/gi, (m, fn, args) =>
      fn + args.replace(/(^|,)(\s*)(["'])([^"']+)\3/g, (x, c, sp, q, u) => `${c}${sp}${q}${map(u)}${q}`) + ')');
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
  // nodeFetch has already decompressed the body (and dropped the length if it did).
  const length = Number(out.get('content-length') || 0);
  out.delete('content-encoding');

  const location = out.get('location');
  if (location) out.set('location', proxUrl(location, target));
  const refresh = out.get('refresh');
  if (refresh) out.set('refresh', rewriteRefresh(refresh, target));

  const cookies = resp.headers.getSetCookie ? resp.headers.getSetCookie() : [];
  out.delete('set-cookie');
  const site = cookieSite(target.hostname);
  for (const c of cookies) out.append('set-cookie', rewriteCookie(c, site, isSecureOrigin(self)));

  const init = { status: resp.status, statusText: resp.statusText, headers: out };
  if (request.method === 'HEAD' || [204, 205, 304].includes(resp.status) || !resp.body) {
    return new Response(null, init);
  }

  const type = (out.get('content-type') || '').toLowerCase();
  if (length > MAX_BUFFERED_BYTES) return new Response(resp.body, init);

  // What the body is used for decides how it is rewritten: a JSONP script
  // served as text/html is still a script.
  // The service worker's re-fetches arrive as "empty"; it passes the real destination along.
  const dest = request.headers.get('x-px-dest') || request.headers.get('sec-fetch-dest') || '';
  const asScript = /^(?:script|worker|sharedworker)$/.test(dest) && !/^(?:image|video|audio|font)\/|css|wasm|json/.test(type);
  const rewritten = (body, mime) => {
    out.delete('content-length');
    // Rewritten text is always sent as UTF-8.
    out.set('content-type', `${mime || type.split(';')[0].trim() || 'text/plain'}; charset=utf-8`);
    return new Response(body, init);
  };

  if (!asScript && /text\/html|application\/xhtml\+xml/.test(type)) {
    const html = decodeText(new Uint8Array(await resp.arrayBuffer()), type, /<meta[^>]+charset=["']?([\w-]+)/i);
    out.set('referrer-policy', 'same-origin');
    out.set('cache-control', 'no-store');
    // XHTML is served as HTML: the injected runtime isn't well-formed XML.
    return rewritten(rewriteHtml(html, target), 'text/html');
  }
  if (type.includes('text/css') && !asScript) {
    const css = decodeText(new Uint8Array(await resp.arrayBuffer()), type, /^@charset\s+["']([\w-]+)/i);
    return rewritten(rewriteCss(css.replace(/^@charset\s+["'][\w-]+["']\s*;?/i, ''), target));
  }
  if (asScript || /javascript|ecmascript/.test(type)) {
    out.set('x-px-js', '1');
    const js = rewriteJs(decodeText(new Uint8Array(await resp.arrayBuffer()), type), target.href, vmCheck);
    return rewritten(/worker$/.test(dest) ? withWorkerRuntime(js) : js, asScript && !/javascript|ecmascript/.test(type) ? 'text/javascript' : null);
  }
  return new Response(resp.body, init);
}

// Decodes text using the charset from a BOM, the Content-Type header or the
// document itself (`sniff`), falling back to UTF-8, then windows-1252 if the
// bytes aren't valid UTF-8 (what browsers usually do for unlabelled pages).
function decodeText(bytes, contentType, sniff) {
  if (bytes[0] === 0xef && bytes[1] === 0xbb && bytes[2] === 0xbf) return new TextDecoder('utf-8').decode(bytes);
  if (bytes[0] === 0xff && bytes[1] === 0xfe) return new TextDecoder('utf-16le').decode(bytes);
  if (bytes[0] === 0xfe && bytes[1] === 0xff) return new TextDecoder('utf-16be').decode(bytes);
  let charset = (/charset=["']?([\w-]+)/i.exec(contentType) || [])[1];
  if (!charset && sniff) {
    const head = new TextDecoder('latin1').decode(bytes.subarray(0, 4096));
    charset = (sniff.exec(head) || [])[1];
    // A document can't really declare itself UTF-16 in ASCII; browsers read that as UTF-8.
    if (/^utf-16/i.test(charset || '')) charset = 'utf-8';
  }
  if (charset) {
    try { return new TextDecoder(charset).decode(bytes); } catch {}
  }
  try {
    return new TextDecoder('utf-8', { fatal: true }).decode(bytes);
  } catch {
    return new TextDecoder('windows-1252').decode(bytes);
  }
}

// Cookies land on the proxy's origin, which every proxied site shares. Each
// one is stored under its site's name ("example.com~sid") with Path=/ and
// only sent back to that site, and made usable inside a cross-site iframe.
function rewriteCookie(cookie, site, secure) {
  const parts = cookie.split(';').map((p) => p.trim()).filter(Boolean);
  if (!parts.length) return cookie;
  const eq = parts[0].indexOf('=');
  const name = eq < 0 ? '' : parts[0].slice(0, eq);
  const kept = [storedCookieName(name, site) + '=' + parts[0].slice(eq + 1)];
  for (const attr of parts.slice(1)) {
    const a = attr.split('=')[0].trim().toLowerCase();
    if (['domain', 'path', 'samesite', 'secure', 'partitioned'].includes(a)) continue;
    kept.push(attr);
  }
  kept.push('Path=/');
  if (secure) kept.push('SameSite=None', 'Secure', 'Partitioned');
  return kept.join('; ');
}

// The site comes first, so __Host-/__Secure- name rules (which need https)
// don't apply to the stored cookie; the attributes they demand are added anyway.
function storedCookieName(name, site) {
  return site + '~' + name;
}

// The Cookie header for one site, with the site names taken off again.
function siteCookies(header, site) {
  const out = [];
  for (const c of (header || '').split(/;\s*/)) {
    const eq = c.indexOf('=');
    if (eq < 0) continue;
    const m = /^([^~]*)~(.*)$/s.exec(c.slice(0, eq));
    if (!m || m[1] !== site) continue;
    const name = m[2];
    out.push(name ? name + c.slice(eq) : c.slice(eq + 1));
  }
  return out.join('; ');
}

// Cookies are shared by a registrable domain (example.com, example.co.uk), approximately.
function cookieSite(hostname) {
  if (/^[\d.]+$|:/.test(hostname)) return hostname;
  const parts = hostname.toLowerCase().replace(/\.$/, '').split('.');
  const sld = parts[parts.length - 2] || '';
  const n = parts.length > 2 && parts[parts.length - 1].length === 2 &&
    /^(?:co|com|net|org|gov|edu|ac|or|ne|go|gob|nic|mil|ltd|plc|sch|nom|info|biz)$/.test(sld) ? 3 : 2;
  return parts.slice(-n).join('.');
}

// Secure / SameSite=None cookies need https (or localhost, which browsers treat as secure).
function isSecureOrigin(self) {
  return self.protocol === 'https:' || ['localhost', '127.0.0.1', '[::1]'].includes(self.hostname);
}

// ---------------------------------------------------------------- HTML

const URL_ATTRS = ['src', 'action', 'formaction', 'poster', 'background'];

// `base` differs from `upstream` for <iframe srcdoc>, whose document is
// about:srcdoc and resolves URLs against its parent's base.
function rewriteHtml(html, upstream, base = upstream) {
  const script = runtimeScript(upstream, PREFIX, false);
  const ctx = { base };
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
      for (const a of ['srcset', 'imagesrcset']) {
        const v = t.get(a);
        if (v != null) t.set(a, proxSrcset(v, ctx.base));
      }
      const xlink = t.get('xlink:href');
      if (xlink != null) t.set('xlink:href', name === 'a' ? proxLink(xlink, ctx.base, upstream) : proxUrl(xlink, ctx.base));
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
        case 'iframe': {
          const doc = t.get('srcdoc');
          if (doc != null) t.set('srcdoc', rewriteHtml(doc, upstream, ctx.base));
          break;
        }
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

const NAMED = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: ' ' };

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
        if (isScript(req)) {
          const tagged = new Request(req, { mode: 'same-origin', headers: withDest(req) });
          e.respondWith(fetch(tagged).then((r) => rewriteResponse(r, url.href.slice(ME.length + PREFIX.length))));
        }
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
  // Re-fetched requests lose their destination, which tells the server to
  // treat the response as a script (and add the worker runtime).
  function withDest(req) {
    const h = new Headers(req.headers);
    if (req.destination) h.set('x-px-dest', req.destination);
    return h;
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
      headers: withDest(req),
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

// ---------------------------------------------------------------- injected worker script

// Runs first in dedicated and shared workers loaded through the proxy, and in
// blob: workers made by proxied pages (blobSite is then the page's site).
// A module worker's static imports are fetched as "worker" too, so each of
// them gets it as well. data: workers don't get it.
function workerRuntime(PREFIX, blobSite) {
  if (self.__px$L) return;
  const real = self.location;
  const ME = real.origin;
  const MEU = new URL(ME);
  const P = ME + PREFIX;
  const WSP = (MEU.protocol === 'https:' ? 'wss://' : 'ws://') + MEU.host + PREFIX;
  let UP;
  try {
    // blob:<proxy>/<id> is reported as blob:<site>/<id>; like a real blob URL,
    // it can't resolve relative URLs.
    if (blobSite) UP = new URL('blob:' + blobSite + real.pathname.slice(real.pathname.lastIndexOf('/')));
    else if (real.href.startsWith(P)) UP = new URL(real.href.slice(P.length));
    else return;
  } catch (e) { return; }

  function prox(u) {
    if (u == null) return u;
    const s = String(u instanceof URL ? u.href : u).trim();
    if (!s || s.startsWith(PREFIX) || s.startsWith(P) || /^(data|blob|javascript|about):/i.test(s)) return u;
    let x;
    try { x = new URL(s, UP.href); } catch (e) { return u; }
    if (x.origin === ME) x = new URL(x.pathname + x.search + x.hash, UP.origin);
    if (x.protocol === 'ws:' || x.protocol === 'wss:') return WSP + x.href;
    return /^https?:$/.test(x.protocol) ? P + x.href : u;
  }
  function unprox(s) {
    if (typeof s !== 'string') return s;
    if (s.startsWith(P)) return s.slice(P.length);
    if (s.startsWith(WSP)) return s.slice(WSP.length);
    return s;
  }
  const hidden = (obj, name, value) => {
    try { Object.defineProperty(obj, name, { value, configurable: true }); } catch (e) {}
  };

  // WorkerLocation is read-only.
  const L = {};
  for (const k of ['href', 'origin', 'protocol', 'host', 'hostname', 'port', 'pathname', 'search', 'hash']) {
    Object.defineProperty(L, k, { get: () => UP[k], enumerable: true });
  }
  L.toString = () => UP.href;
  L[Symbol.toStringTag] = 'WorkerLocation';
  hidden(self, '__px$L', L);
  hidden(self, '__px$origin', UP.origin);
  hidden(self, '__px$u', (u, base) => {
    if (typeof u !== 'string' && !(u instanceof URL)) return u;
    try { return prox(new URL(String(u), base || UP.href).href); } catch (e) { return u; }
  });
  try { Object.defineProperty(self, 'origin', { get: () => UP.origin, configurable: true }); } catch (e) {}

  const _fetch = self.fetch;
  const reqUrl = Object.getOwnPropertyDescriptor(Request.prototype, 'url').get;
  self.fetch = async function (input, init) {
    if (input instanceof Request) {
      const r = input;
      const p = prox(reqUrl.call(r));
      if (p !== reqUrl.call(r)) {
        const o = {
          method: r.method, headers: r.headers, credentials: r.credentials, cache: r.cache,
          redirect: r.redirect, referrer: r.referrer, referrerPolicy: r.referrerPolicy,
          keepalive: r.keepalive, signal: r.signal, mode: r.mode,
        };
        if (r.body && !(init && 'body' in init)) o.body = await r.arrayBuffer();
        input = new Request(p, o);
      }
    } else {
      input = prox(input);
    }
    return _fetch.call(this, input, init);
  };
  if (self.XMLHttpRequest) {
    const _open = XMLHttpRequest.prototype.open;
    XMLHttpRequest.prototype.open = function (method, url, ...rest) { return _open.call(this, method, prox(url), ...rest); };
  }
  if (self.importScripts) {
    const _import = self.importScripts;
    self.importScripts = function (...urls) { return _import.apply(this, urls.map(prox)); };
  }
  for (const name of ['WebSocket', 'EventSource', 'Worker', 'SharedWorker']) {
    const Orig = self[name];
    if (!Orig) continue;
    self[name] = new Proxy(Orig, {
      construct(target, args, newTarget) {
        if (name === 'WebSocket' && args.length) {
          try {
            const x = new URL(String(args[0] instanceof URL ? args[0].href : args[0]), UP.href);
            if (/^https?:$/.test(x.protocol)) x.protocol = x.protocol === 'https:' ? 'wss:' : 'ws:';
            args[0] = x.href;
          } catch (e) {}
        }
        if (args.length) args[0] = prox(args[0]);
        return Reflect.construct(target, args, newTarget);
      },
    });
  }
  const GETTERS = [['Response', 'url'], ['Request', 'url'], ['XMLHttpRequest', 'responseURL'],
    ['WebSocket', 'url'], ['EventSource', 'url'], ['PerformanceEntry', 'name']];
  for (const [cls, prop] of GETTERS) {
    const proto = self[cls] && self[cls].prototype;
    const desc = proto && Object.getOwnPropertyDescriptor(proto, prop);
    if (!desc || !desc.get) continue;
    Object.defineProperty(proto, prop, { ...desc, get() { return unprox(desc.get.call(this)); } });
  }
}

const WORKER_PRELUDE = `(function(__name){(${workerRuntime})(${JSON.stringify(PREFIX)});})(function(f){return f;});`;

// A leading "use strict" must stay first to keep applying to the script.
function withWorkerRuntime(js) {
  const strict = /^\s*(?:(?:\/\/[^\n]*|\/\*[\s\S]*?\*\/)\s*)*(['"])use strict\1/.test(js);
  return (strict ? '"use strict";' : '') + WORKER_PRELUDE + '\n' + js;
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
function runtime(C, rewriteJs, mapSrcset, rewriteCss, workerRuntime) {
  // A frame's initial about:blank window is reused when it navigates to a
  // same-origin page, keeping everything installed here. The new document's
  // runtime then only switches the existing one over to its site.
  if (window.__pxRuntime) {
    if (!document.__px$L) window.__pxRuntime(C);
    return;
  }

  // location.origin is "null" in about:blank / srcdoc frames; self.origin is the
  // document's real (inherited) origin and isn't patched yet at this point.
  const ME = self.origin && self.origin !== 'null' ? self.origin : location.origin;
  const MEU = new URL(ME);
  const P = ME + C.prefix;
  const WSP = (MEU.protocol === 'https:' ? 'wss://' : 'ws://') + MEU.host + C.prefix;
  let UP = new URL(C.upstream);
  const fnSource = Function.prototype.toString;
  const baseDesc = Object.getOwnPropertyDescriptor(Node.prototype, 'baseURI');
  const _getAttr = Element.prototype.getAttribute;
  const _replaceState = history.replaceState;

  let nested = false;
  try { nested = window.parent !== window && !!window.parent.__pxRuntime; } catch (e) {}

  // Upstream URL of the current document / base.
  function upHere() {
    if (location.href.startsWith(P)) return location.href.slice(P.length);
    if (location.protocol === 'about:') return location.href;
    return UP.origin + location.pathname + location.search + location.hash;
  }
  function upBase() {
    const b = baseDesc.get.call(document);
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
      return WSP + x.href;
    }
    return P + x.href;
  }

  function proxSrcset(v) {
    return mapSrcset(v, prox);
  }
  function unproxSrcset(v) {
    return mapSrcset(v, unproxAttr);
  }

  // Secure / SameSite=None cookies need https (or localhost, which browsers treat as secure).
  const secureCtx = MEU.protocol === 'https:' || ['localhost', '127.0.0.1', '[::1]'].includes(MEU.hostname);
  const cookieAttrs = '; path=/' + (secureCtx ? '; SameSite=None; Secure; Partitioned' : '');


  // Storage. Cookies, localStorage, sessionStorage and IndexedDB all belong to
  // the proxy's origin, which every proxied site shares, so each site gets its
  // own namespace. Cookies match the server's naming ("example.com~sid").
  let CS = C.cookieSite + '~';
  const cookieDesc = Object.getOwnPropertyDescriptor(Document.prototype, 'cookie');
  if (cookieDesc && cookieDesc.get && cookieDesc.set) {
    Object.defineProperty(Document.prototype, 'cookie', {
      ...cookieDesc,
      get() {
        return cookieDesc.get.call(this).split(/;\s*/).filter((c) => c.startsWith(CS))
          .map((c) => c.slice(CS.length).replace(/^=/, '')).join('; ');
      },
      set(v) {
        const parts = String(v).split(';').map((x) => x.trim()).filter(Boolean);
        if (!parts.length) return;
        const kept = [CS + (parts[0].includes('=') ? parts[0] : '=' + parts[0])];
        for (const attr of parts.slice(1)) {
          const a = attr.split('=')[0].trim().toLowerCase();
          if (!['domain', 'path', 'samesite', 'secure', 'partitioned'].includes(a)) kept.push(attr);
        }
        cookieDesc.set.call(this, kept.join('; ') + cookieAttrs);
      },
    });
  }
  // The async Cookie Store API can't be namespaced the same way; sites fall back to document.cookie.
  try { delete window.cookieStore; } catch (e) {}
  try { if ('cookieStore' in window) Object.defineProperty(window, 'cookieStore', { value: undefined, configurable: true }); } catch (e) {}

  let SP = UP.origin + '~';
  for (const name of ['localStorage', 'sessionStorage']) {
    let st;
    try { st = window[name]; } catch (e) { continue; }
    if (!st) continue;
    const keys = () => {
      const out = [];
      for (let i = 0; i < st.length; i++) {
        const k = st.key(i);
        if (k != null && k.startsWith(SP)) out.push(k.slice(SP.length));
      }
      return out;
    };
    const api = {
      getItem: (k) => st.getItem(SP + k),
      setItem: (k, v) => st.setItem(SP + k, v),
      removeItem: (k) => st.removeItem(SP + k),
      clear: () => keys().forEach((k) => st.removeItem(SP + k)),
      key: (i) => { const k = keys()[i]; return k === undefined ? null : k; },
    };
    const facade = new Proxy(st, {
      get(t, p) {
        if (p === 'length') return keys().length;
        if (typeof p === 'string' && Object.prototype.hasOwnProperty.call(api, p)) return api[p];
        if (typeof p === 'symbol' || p in Storage.prototype) {
          const v = Reflect.get(t, p);
          return typeof v === 'function' ? v.bind(t) : v;
        }
        const v = st.getItem(SP + p);
        return v === null ? undefined : v;
      },
      set(t, p, v) {
        if (typeof p !== 'string') return false;
        st.setItem(SP + p, v);
        return true;
      },
      has(t, p) {
        return typeof p === 'string' && (p in Storage.prototype || st.getItem(SP + p) !== null);
      },
      deleteProperty(t, p) {
        if (typeof p === 'string') st.removeItem(SP + p);
        return true;
      },
      defineProperty(t, p, d) {
        if (typeof p === 'string' && 'value' in d) st.setItem(SP + p, d.value);
        return true;
      },
      ownKeys: () => keys(),
      getOwnPropertyDescriptor(t, p) {
        const v = typeof p === 'string' ? st.getItem(SP + p) : null;
        return v === null ? undefined : { value: v, writable: true, enumerable: true, configurable: true };
      },
    });
    try { Object.defineProperty(window, name, { get: () => facade, configurable: true, enumerable: true }); } catch (e) {}
  }
  const unSP = (k) => (typeof k === 'string' && k.startsWith(SP) ? k.slice(SP.length) : k);
  const skDesc = window.StorageEvent && Object.getOwnPropertyDescriptor(StorageEvent.prototype, 'key');
  if (skDesc && skDesc.get) {
    Object.defineProperty(StorageEvent.prototype, 'key', { ...skDesc, get() { return unSP(skDesc.get.call(this)); } });
  }
  if (window.IDBFactory) {
    const f = IDBFactory.prototype;
    const { open: idbOpen, deleteDatabase: idbDelete, databases: idbList } = f;
    f.open = function (n, ...rest) { return idbOpen.call(this, SP + n, ...rest); };
    f.deleteDatabase = function (n, ...rest) { return idbDelete.call(this, SP + n, ...rest); };
    if (idbList) {
      f.databases = function () {
        return idbList.call(this).then((l) => l.filter((d) => d.name.startsWith(SP)).map((d) => ({ ...d, name: unSP(d.name) })));
      };
    }
    const nameDesc = Object.getOwnPropertyDescriptor(IDBDatabase.prototype, 'name');
    if (nameDesc && nameDesc.get) {
      Object.defineProperty(IDBDatabase.prototype, 'name', { ...nameDesc, get() { return unSP(nameDesc.get.call(this)); } });
    }
  }

  // Network APIs
  // Streamed request bodies need HTTP/2, which the proxy may not be served
  // over (e.g. plain Node on http://), so read them into a buffer first.
  const isStream = (b) => typeof ReadableStream !== 'undefined' && b instanceof ReadableStream;
  const _fetch = window.fetch;
  const reqUrl = Object.getOwnPropertyDescriptor(Request.prototype, 'url').get;
  window.fetch = async function (input, init) {
    if (init && isStream(init.body)) {
      init = { ...init, body: await new Response(init.body).arrayBuffer() };
      delete init.duplex;
    }
    if (input instanceof Request) {
      const r = input;
      const u = reqUrl.call(r);
      const p = prox(u);
      const hasBody = !!r.body && !(init && 'body' in init);
      if (p !== u || hasBody) {
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

  // blob: workers never reach the server or service worker, so remember each
  // blob's Blob and start such workers from a wrapper that runs the worker
  // runtime first. Classic workers then importScripts the original (keeping
  // its "use strict"); module workers import it after the runtime. Wrappers
  // are reused per URL so SharedWorkers stay shared, and are never revoked
  // because the worker may not have loaded them yet.
  const blobs = new Map();
  const wrappers = new Map();
  const _createURL = URL.createObjectURL;
  const _revokeURL = URL.revokeObjectURL;
  URL.createObjectURL = function (obj) {
    const url = _createURL.call(this, obj);
    if (obj instanceof Blob) blobs.set(url, obj);
    return url;
  };
  URL.revokeObjectURL = function (url) {
    blobs.delete(String(url));
    return _revokeURL.call(this, url);
  };
  function blobWorker(u, opts) {
    const s = String(u instanceof URL ? u.href : u);
    const blob = blobs.get(s);
    if (!blob) return u;
    const module = !!opts && typeof opts === 'object' && opts.type === 'module';
    const key = (module ? 'm ' : 'c ') + s;
    if (!wrappers.has(key)) {
      const pre = '(function(__name){(' + fnSource.call(workerRuntime) + ')(' + JSON.stringify(C.prefix) + ','
        + JSON.stringify(UP.origin) + ');})(function(f){return f;});\n';
      const js = (parts) => _createURL(new Blob(parts, { type: 'text/javascript' }));
      const orig = JSON.stringify(_createURL(blob));
      wrappers.set(key, module
        ? js(['import ' + JSON.stringify(js([pre])) + ';import ' + orig + ';'])
        : js([pre + 'importScripts(' + orig + ');']));
    }
    return wrappers.get(key);
  }

  for (const name of ['WebSocket', 'EventSource', 'Worker', 'SharedWorker']) {
    const Orig = window[name];
    if (!Orig) continue;
    window[name] = new Proxy(Orig, {
      construct(target, args, newTarget) {
        // WebSocket also takes http(s) and relative URLs, meaning ws(s) on the site.
        if (name === 'WebSocket' && args.length) {
          try {
            const x = new URL(String(args[0] instanceof URL ? args[0].href : args[0]), upBase());
            if (/^https?:$/.test(x.protocol)) x.protocol = x.protocol === 'https:' ? 'wss:' : 'ws:';
            args[0] = x.href;
          } catch (e) {}
        }
        if (args.length && /Worker$/.test(name)) args[0] = blobWorker(args[0], args[1]);
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
  window.open = function (url, name, ...rest) {
    const t = frameTarget(name);
    return _wopen.call(this, url == null || url === '' ? url : prox(url), t == null ? name : t, ...rest);
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
  // Only the proxied frames count as ancestors, under their sites' origins.
  Object.defineProperty(L, 'ancestorOrigins', {
    get() {
      const l = [];
      try { for (let w = window; w !== pxTop;) { w = w.parent; l.push(w.__px$origin); } } catch (e) {}
      return Object.freeze(Object.assign(l, { item: (i) => (l[i] === undefined ? null : l[i]), contains: (o) => l.includes(o) }));
    },
  });
  L.assign = (u) => go(u);
  L.replace = (u) => go(u, true);
  L.reload = () => real.reload();
  L.toString = upHere;
  L[Symbol.toStringTag] = 'Location';

  let pxTop = window;
  try { while (pxTop.parent !== pxTop && pxTop.parent.__pxRuntime) pxTop = pxTop.parent; } catch (e) {}

  // _top and _parent would leave the proxy for the page embedding it; aim
  // them at the outermost proxied frame instead. Returns null if unchanged.
  function frameTarget(t) {
    const n = String(t || '').toLowerCase();
    if (n === '_top' && pxTop !== window) {
      try {
        if (!pxTop.name) pxTop.name = '__px_top';
        return pxTop.name;
      } catch (e) { return '_self'; }
    }
    if (n === '_top' || (n === '_parent' && !nested)) return '_self';
    return null;
  }
  const baseTarget = () => { const b = document.querySelector('base[target]'); return b ? b.getAttribute('target') : ''; };
  addEventListener('submit', (e) => {
    const f = e.target;
    if (!(f instanceof HTMLFormElement)) return;
    const s = e.submitter;
    if (s && s.hasAttribute('formtarget')) {
      const t = frameTarget(s.getAttribute('formtarget'));
      if (t != null) _setAttr.call(s, 'formtarget', t);
      return;
    }
    const t = frameTarget(f.getAttribute('target') || baseTarget());
    if (t != null) _setAttr.call(f, 'target', t);
  }, true);
  const _submit = HTMLFormElement.prototype.submit; // doesn't fire 'submit'
  HTMLFormElement.prototype.submit = function () {
    const t = frameTarget(this.getAttribute('target') || baseTarget());
    if (t != null) _setAttr.call(this, 'target', t);
    return _submit.call(this);
  };
  const _F = Function;
  const jsCheck = (c) => { try { new _F(c); return true; } catch (e) { return false; } };
  const js = (s) => (typeof s === 'string' ? rewriteJs(s, upBase(), jsCheck) : s);
  const hidden = (obj, name, value) => {
    try { Object.defineProperty(obj, name, { value, configurable: true }); } catch (e) {}
  };
  hidden(window, '__px$L', L);
  hidden(window, '__px$top', pxTop);
  hidden(window, '__px$parent', nested ? window.parent : window);
  hidden(window, '__px$origin', UP.origin);
  hidden(window, '__pxRuntime', (c) => {
    C = c;
    UP = new URL(C.upstream);
    CS = C.cookieSite + '~';
    SP = UP.origin + '~';
    hidden(window, '__px$origin', UP.origin);
    perDoc();
  });
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
    if (typeof s !== 'string') return s;
    if (s.startsWith(P)) return s.slice(P.length);
    if (s.startsWith(WSP)) return s.slice(WSP.length);
    if (s === ME || s.startsWith(ME + '/')) return UP.origin + s.slice(ME.length);
    return s;
  }
  // Attribute values: only undo what the proxy wrote.
  function unproxAttr(s) {
    if (typeof s !== 'string' || !s.includes(C.prefix)) return s;
    if (s.startsWith(C.prefix)) return s.slice(C.prefix.length);
    return s.startsWith(P) || s.startsWith(WSP) ? unprox(s) : s;
  }
  const own = (obj, name, get) => {
    try { Object.defineProperty(obj, name, { get, configurable: true }); } catch (e) {}
  };
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


  // DOM URL attributes. Links (<a>, <area>) are left alone so routers can read
  // real paths; the click handler below routes them through the proxy.
  const isLink = (el) => el instanceof HTMLAnchorElement || el instanceof HTMLAreaElement;
  const URL_ATTRS = new Set(['src', 'href', 'action', 'formaction', 'poster', 'data']);
  const _setAttr = Element.prototype.setAttribute;
  Element.prototype.setAttribute = function (name, value) {
    const n = String(name).toLowerCase();
    if (URL_ATTRS.has(n) && !isLink(this)) value = prox(value);
    else if (n === 'srcset' || n === 'imagesrcset') value = proxSrcset(value);
    else if (n === 'integrity') return;
    else if (n === 'srcdoc' && this instanceof HTMLIFrameElement) value = withRuntime(value);
    else if (n === 'style') value = proxCss(value);
    else if (n.startsWith('on')) value = js(String(value));
    return _setAttr.call(this, name, value);
  };
  const _setAttrNS = Element.prototype.setAttributeNS;
  Element.prototype.setAttributeNS = function (ns, name, value) {
    const n = String(name).toLowerCase().replace(/^.*:/, '');
    if (URL_ATTRS.has(n) && !isLink(this)) value = prox(value);
    return _setAttrNS.call(this, ns, name, value);
  };

  const PROPS = [
    ['HTMLScriptElement', 'src'], ['HTMLImageElement', 'src'], ['HTMLImageElement', 'srcset', proxSrcset],
    ['HTMLSourceElement', 'src'], ['HTMLSourceElement', 'srcset', proxSrcset], ['HTMLMediaElement', 'src'],
    ['HTMLIFrameElement', 'src'], ['HTMLEmbedElement', 'src'], ['HTMLTrackElement', 'src'],
    ['HTMLLinkElement', 'href'], ['HTMLFormElement', 'action'], ['HTMLVideoElement', 'poster'],
    ['HTMLObjectElement', 'data'], ['HTMLLinkElement', 'imageSrcset', proxSrcset],
  ];
  for (const [cls, prop, fn = prox] of PROPS) {
    const proto = window[cls] && window[cls].prototype;
    const desc = proto && Object.getOwnPropertyDescriptor(proto, prop);
    if (!desc || !desc.set) continue;
    const un = fn === prox ? unprox : unproxSrcset;
    Object.defineProperty(proto, prop, {
      ...desc,
      get() { return un(desc.get.call(this)); },
      set(v) { desc.set.call(this, fn(v)); },
    });
  }
  // Read-only URLs the page can see.
  const GETTERS = [
    ['HTMLImageElement', 'currentSrc'], ['HTMLMediaElement', 'currentSrc'], ['Node', 'baseURI'],
    ['Response', 'url'], ['Request', 'url'], ['XMLHttpRequest', 'responseURL'], ['WebSocket', 'url'],
    ['EventSource', 'url'], ['PerformanceEntry', 'name'], ['StyleSheet', 'href'],
  ];
  for (const [cls, prop] of GETTERS) {
    const proto = window[cls] && window[cls].prototype;
    const desc = proto && Object.getOwnPropertyDescriptor(proto, prop);
    if (!desc || !desc.get) continue;
    Object.defineProperty(proto, prop, { ...desc, get() { return unprox(desc.get.call(this)); } });
  }
  Element.prototype.getAttribute = function (name) {
    const v = _getAttr.call(this, name);
    if (v == null || !v.includes(C.prefix)) return v;
    const n = String(name).toLowerCase();
    if (URL_ATTRS.has(n)) return unproxAttr(v);
    if (n === 'srcset' || n === 'imagesrcset') return mapSrcset(v, unproxAttr);
    return v;
  };

  // Frames the page creates start as about:blank (or srcdoc) documents on our
  // origin with none of the patches above, and sites borrow clean fetch, XHR
  // or location from them. They get this runtime too, set to this page's site.
  const runtimeCode = () => '(function(__name){(' + fnSource.call(runtime) + ')('
    + JSON.stringify({ ...C, upstream: location.protocol === 'about:' ? C.upstream : upHere(), swReload: false }).replace(/</g, '\\u003c') + ','
    + fnSource.call(rewriteJs) + ',' + fnSource.call(mapSrcset) + ',' + fnSource.call(rewriteCss) + ','
    + fnSource.call(workerRuntime) + ');})(function(f){return f;});';
  const RT_TAG = /^(\s*<!doctype[^>]*>)?\s*<script data-px-rt>[\s\S]*?<\/script>/i;
  const withRuntime = (html) => String(html).replace(RT_TAG, '$1').replace(/^(\s*<!doctype[^>]*>)?/i,
    (m) => m + '<script data-px-rt>' + runtimeCode().replace(/<\/(script)/gi, '<\\/$1') + '<\/script>');
  function adopt(frame, w) {
    try {
      if (!w || w.__pxRuntime || frame.hasAttribute('srcdoc')) return;
      // A pending src navigation brings its own runtime (and may reuse this window).
      const src = (_getAttr.call(frame, 'src') || '').trim();
      if (src && !/^about:blank$/i.test(src)) return;
      if (w.location.protocol !== 'about:') return;
      w.eval(runtimeCode());
    } catch (e) {}
  }
  for (const prop of ['contentWindow', 'contentDocument']) {
    const desc = Object.getOwnPropertyDescriptor(HTMLIFrameElement.prototype, prop);
    if (!desc || !desc.get) continue;
    const cw = Object.getOwnPropertyDescriptor(HTMLIFrameElement.prototype, 'contentWindow').get;
    Object.defineProperty(HTMLIFrameElement.prototype, prop, {
      ...desc,
      get() { adopt(this, cw.call(this)); return desc.get.call(this); },
    });
  }
  const srcdocDesc = Object.getOwnPropertyDescriptor(HTMLIFrameElement.prototype, 'srcdoc');
  if (srcdocDesc && srcdocDesc.set) {
    Object.defineProperty(HTMLIFrameElement.prototype, 'srcdoc', {
      ...srcdocDesc,
      get() { return srcdocDesc.get.call(this).replace(RT_TAG, '$1'); },
      set(v) { srcdocDesc.set.call(this, withRuntime(v)); },
    });
  }

  // CSS added at runtime: <style> text, style attributes and the CSSOM. Rules
  // in an external sheet resolve against that sheet's (upstream) URL.
  function proxCss(css, base) {
    const s = String(css);
    if (!/url\(|@import|image-set\(/i.test(s)) return s;
    return rewriteCss(s, null, (u) => {
      if (!base || /^\s*#/.test(u)) return prox(u);
      try { return prox(new URL(u.trim(), base).href); } catch (e) { return u; }
    });
  }
  const sheetBase = (sheet) => (sheet && sheet.href ? unprox(sheet.href) : null);
  function fixStyle(el) {
    const v = el.textContent;
    const nv = proxCss(v);
    if (nv !== v) el.textContent = nv;
  }
  if (window.CSSStyleSheet) {
    const CSP = CSSStyleSheet.prototype;
    for (const m of ['insertRule', 'replace', 'replaceSync']) {
      const orig = CSP[m];
      if (orig) CSP[m] = function (css, ...rest) { return orig.call(this, proxCss(css, sheetBase(this)), ...rest); };
    }
  }
  if (window.CSSStyleDeclaration) {
    const SDP = CSSStyleDeclaration.prototype;
    const setProp = SDP.setProperty;
    SDP.setProperty = function (name, value, ...rest) {
      return setProp.call(this, name, value == null ? value : proxCss(value, sheetBase(this.parentRule && this.parentRule.parentStyleSheet)), ...rest);
    };
    const cssTextDesc = Object.getOwnPropertyDescriptor(SDP, 'cssText');
    if (cssTextDesc && cssTextDesc.set) {
      Object.defineProperty(SDP, 'cssText', { ...cssTextDesc, set(v) { cssTextDesc.set.call(this, proxCss(v)); } });
    }
  }

  // Elements inserted via innerHTML bypass the setters above.
  const ATTRS = { src: prox, srcset: proxSrcset, imagesrcset: proxSrcset, poster: prox, action: prox, data: prox };
  function fixTree(root) {
    if (root.nodeType === 3 && root.parentNode instanceof HTMLStyleElement) return fixStyle(root.parentNode);
    if (root.nodeType !== 1) return;
    if (root instanceof HTMLStyleElement) fixStyle(root);
    else for (const st of root.getElementsByTagName('style')) fixStyle(st);
    if (root.hasAttribute('style')) fixStyleAttr(root);
    for (const el of root.querySelectorAll('[style]')) fixStyleAttr(el);
    const els = [root, ...root.querySelectorAll('[src],[srcset],[imagesrcset],[poster],[action],link[href],object[data],iframe')];
    for (const el of els) {
      if (el instanceof HTMLIFrameElement) adopt(el, el.contentWindow);
      for (const a in ATTRS) {
        const v = _getAttr.call(el, a);
        if (v != null) {
          const nv = ATTRS[a](v);
          if (nv !== v) _setAttr.call(el, a, nv);
        }
      }
      if (el instanceof HTMLLinkElement) {
        const v = _getAttr.call(el, 'href');
        const nv = v != null && prox(v);
        if (nv && nv !== v) _setAttr.call(el, 'href', nv);
      }
      if (el.hasAttribute && el.hasAttribute('integrity')) el.removeAttribute('integrity');
    }
  }
  function fixStyleAttr(el) {
    const v = _getAttr.call(el, 'style');
    const nv = v && proxCss(v);
    if (nv && nv !== v) _setAttr.call(el, 'style', nv);
  }
  const observer = new MutationObserver((records) => {
    for (const r of records) {
      // el.style.backgroundImage = ... only shows up as a style attribute change.
      if (r.type === 'attributes') fixStyleAttr(r.target);
      else for (const n of r.addedNodes) fixTree(n);
    }
  });

  // Route link clicks through the proxy if no router handled them.
  addEventListener('click', (e) => {
    if (e.defaultPrevented) return;
    const a = e.target && e.target.closest && e.target.closest('a[href], area[href]');
    if (!a || a.hasAttribute('download')) return;
    const raw = _getAttr.call(a, 'href');
    if (!raw || raw[0] === '#' || isProxied(raw)) return;
    let x;
    try { x = new URL(a.href); } catch (err) { return; } // the site's URL (see the href getter above)
    if (!/^https?:$/.test(x.protocol)) return;
    const here = new URL(upHere());
    if (x.hash && x.origin === here.origin && x.pathname === here.pathname && x.search === here.search) return;
    const t = frameTarget(a.getAttribute('target') || baseTarget());
    if (t != null) _setAttr.call(a, 'target', t);
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

  // Per document: a reused window gets a new one.
  function perDoc() {
    const ref = document.referrer;
    hidden(document, '__px$L', L);
    own(document, 'URL', upHere);
    own(document, 'documentURI', upHere);
    own(document, 'referrer', () => (ref.startsWith(ME + '/') ? unprox(ref) : ''));
    try {
      Object.defineProperty(document, 'domain', { get: () => UP.hostname, set: () => {}, configurable: true });
    } catch (e) {}
    observer.observe(document, { childList: true, subtree: true, attributes: true, attributeFilter: ['style'] });
    // Outermost proxied frame: show the real path and remember the site.
    if (!nested) {
      if (location.href.startsWith(P)) {
        const real = new URL(upHere());
        if (real.origin === UP.origin) _replaceState.call(history, history.state, '', real.pathname + real.search + real.hash);
      }
      try {
        cookieDesc.set.call(document, '__px_origin=' + encodeURIComponent(UP.origin) + cookieAttrs);
      } catch (e) {}
    }
  }
  perDoc();
}

function runtimeScript(upstream, prefix, swReload) {
  const json = JSON.stringify({
    upstream: upstream.href, prefix, swReload, cookieSite: cookieSite(upstream.hostname),
  }).replace(/</g, '\\u003c');
  // __name: guard against bundlers that wrap functions with a name helper.
  return `<script data-px-rt>(function(__name){(${runtime})(${json},${rewriteJs},${mapSrcset},${rewriteCss},${workerRuntime});})(function(f){return f;});</script>`;
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

const server = http.createServer({ maxHeaderSize: 256 * 1024 }, async (req, res) => {
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
const WS_TIMEOUT = 30_000;

function upstreamSocket(target, port, secure, ca) {
  return new Promise((resolve, reject) => {
    const s = secure
      ? tls.connect({ host: target.hostname, port, servername: target.hostname, ALPNProtocols: ['http/1.1'], lookup: safeLookup, ...(ca && { ca }) })
      : net.connect({ host: target.hostname, port, lookup: safeLookup });
    s.setTimeout(WS_TIMEOUT, () => s.destroy(Object.assign(new Error('timeout'), { code: 'ETIMEDOUT' })));
    s.once(secure ? 'secureConnect' : 'connect', () => { s.setTimeout(0); s.removeListener('error', reject); s.on('error', () => {}); resolve(s); });
    s.once('error', reject);
  });
}

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
    let closed = false;
    socket.once('close', () => { closed = true; });
    const key = `${target.hostname}:${port}`;
    let ca = secure && hostAgents.has(key) ? (await chainAgent(target.hostname, port))?.options.ca : undefined;
    let up;
    try {
      up = await upstreamSocket(target, port, secure, ca);
    } catch (err) {
      // Same incomplete-chain fallback as nodeFetch().
      if (!secure || ca || !CHAIN_ERRORS.has(err.code)) throw err;
      ca = (await chainAgent(target.hostname, port))?.options.ca;
      if (!ca) throw err;
      up = await upstreamSocket(target, port, secure, ca);
    }
    if (closed) { up.destroy(); return; }

    const lines = [`GET ${target.pathname}${target.search} HTTP/1.1`, `Host: ${target.host}`,
      'Connection: Upgrade', 'Upgrade: websocket'];
    for (const [k, v] of upstreamHeaders(request, self, target)) lines.push(`${k}: ${v}`);

    // Keep the timeout until the upstream answers the handshake.
    up.setTimeout(WS_TIMEOUT, () => up.destroy());
    up.once('data', () => up.setTimeout(0));
    up.write(lines.join('\r\n') + '\r\n\r\n');
    if (head && head.length) up.write(head);
    up.pipe(socket);
    socket.pipe(up);
    up.on('error', () => socket.destroy());
    up.on('close', () => socket.destroy());
    socket.on('close', () => up.destroy());
  } catch {
    // Upstream unreachable (or bad TLS): answer like the HTTP path does.
    if (socket.writable) socket.end('HTTP/1.1 502 Bad Gateway\r\nConnection: close\r\n\r\n');
    else socket.destroy();
  }
});

// Imported (e.g. by index.test.js) it only provides the exports below.
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  server.listen(PORT, HOST, () => {
    console.log(`Peekaboom listening on http://localhost:${PORT}`);
  });
}

export {
  server, rewriteHtml, rewriteCss, rewriteJs, mapSrcset, proxUrl, rewriteCookie, siteCookies, cookieSite,
  decodeText, runtimeScript, withWorkerRuntime,
};
