/*
 * build-sw.js - 서비스 워커(sw.js)를 파일 목록에서 다시 만든다.
 *
 *   오프라인으로 돌리려면 서비스 워커가 어떤 파일을 미리 받아 둘지 알아야 하고,
 *   파일이 하나라도 바뀌면 캐시 이름이 달라져야 방문자에게 갱신이 전달된다.
 *   그 두 가지를 손으로 관리하지 않도록 여기서 자동으로 만든다.
 *
 *   실행: node build-sw.js
 *   CI 는 이걸 돌린 뒤 `git diff --exit-code sw.js` 로 최신인지 확인한다.
 */
var fs = require('fs');
var path = require('path');
var crypto = require('crypto');

var ROOT = __dirname;

// 사이트가 돌아가는 데 실제로 필요한 것만. generate.js·verify.js 같은
// 개발용 파일은 캐시에도 넣지 않고 배포에도 올리지 않는다.
var RUNTIME_FILES = [
  'index.html',
  'styles.css',
  'app.js',
  'parser.js',
  'problems.js',
  'manifest.webmanifest',
  'icons/icon-192.png',
  'icons/icon-512.png',
  'icons/maskable-512.png',
  'icons/apple-touch-icon.png'
];

function walk(dir, out) {
  fs.readdirSync(dir).forEach(function (name) {
    var full = path.join(dir, name);
    if (fs.statSync(full).isDirectory()) walk(full, out);
    else out.push(path.relative(ROOT, full).split(path.sep).join('/'));
  });
  return out;
}

var assets = RUNTIME_FILES.concat(walk(path.join(ROOT, 'vendor'), []).sort());

var missing = assets.filter(function (f) { return !fs.existsSync(path.join(ROOT, f)); });
if (missing.length) {
  console.error('없는 파일: ' + missing.join(', '));
  process.exit(1);
}

// 내용이 바뀌면 캐시 이름도 바뀐다
var h = crypto.createHash('sha256');
assets.forEach(function (f) {
  h.update(f);
  h.update(fs.readFileSync(path.join(ROOT, f)));
});
var version = h.digest('hex').slice(0, 12);

var sw = [
  '/*',
  ' * sw.js - 오프라인 서비스 워커 (자동 생성 파일).',
  ' *',
  ' *   직접 고치지 말고 build-sw.js 를 고친 뒤 `node build-sw.js` 를 다시 실행할 것.',
  ' *   설치할 때 아래 파일을 전부 받아 두므로, 한 번 연 뒤에는 네트워크 없이 돌아간다.',
  ' */',
  "var VERSION = '" + version + "';",
  "var CACHE = 'daily-integral-' + VERSION;",
  '',
  'var ASSETS = [',
  assets.map(function (f) { return "  '" + f + "'"; }).join(',\n'),
  '];',
  '',
  '// 설치 즉시 전부 받아 둔다',
  "self.addEventListener('install', function (e) {",
  '  e.waitUntil(',
  '    caches.open(CACHE)',
  "      .then(function (c) { return c.addAll(ASSETS.concat(['./'])); })",
  '      .then(function () { return self.skipWaiting(); })',
  '  );',
  '});',
  '',
  '// 새 버전이 활성화되면 옛 캐시를 지운다',
  "self.addEventListener('activate', function (e) {",
  '  e.waitUntil(',
  '    caches.keys()',
  '      .then(function (keys) {',
  '        return Promise.all(keys.map(function (k) {',
  "          return (k !== CACHE && k.indexOf('daily-integral-') === 0) ? caches.delete(k) : null;",
  '        }));',
  '      })',
  '      .then(function () { return self.clients.claim(); })',
  '  );',
  '});',
  '',
  '// 캐시 우선. 네트워크는 뒤에서 조용히 갱신만 한다(stale-while-revalidate).',
  '// 문제 은행이 통째로 정적 파일이라 이 전략이면 오프라인에서 기능이 하나도 빠지지 않는다.',
  "self.addEventListener('fetch', function (e) {",
  '  var req = e.request;',
  "  if (req.method !== 'GET') return;",
  '  var url = new URL(req.url);',
  '  if (url.origin !== self.location.origin) return;',
  '',
  '  e.respondWith(',
  '    caches.open(CACHE).then(function (cache) {',
  '      return cache.match(req).then(function (hit) {',
  '        var net = fetch(req).then(function (res) {',
  '          if (res && res.ok) cache.put(req, res.clone());',
  '          return res;',
  '        }).catch(function () { return null; });',
  '',
  '        // 캐시에 있으면 바로 준다',
  '        if (hit) return hit;',
  '',
  '        // 없으면 네트워크를 기다리고, 그것도 안 되면 문서 요청은 첫 화면으로 돌린다',
  '        return net.then(function (res) {',
  '          if (res) return res;',
  "          if (req.mode === 'navigate') return cache.match('index.html');",
  "          return new Response('', { status: 504, statusText: 'offline' });",
  '        });',
  '      });',
  '    })',
  '  );',
  '});',
  ''
].join('\n');

fs.writeFileSync(path.join(ROOT, 'sw.js'), sw);
console.log('sw.js 갱신 — ' + assets.length + '개 파일, 버전 ' + version);
