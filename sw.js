/*
 * sw.js - 오프라인 서비스 워커 (자동 생성 파일).
 *
 *   직접 고치지 말고 build-sw.js 를 고친 뒤 `node build-sw.js` 를 다시 실행할 것.
 *   설치할 때 아래 파일을 전부 받아 두므로, 한 번 연 뒤에는 네트워크 없이 돌아간다.
 */
var VERSION = '4e349404e079';
var CACHE = 'daily-integral-' + VERSION;

var ASSETS = [
  'index.html',
  'styles.css',
  'app.js',
  'parser.js',
  'problems.js',
  'manifest.webmanifest',
  'icons/icon-192.png',
  'icons/icon-512.png',
  'icons/maskable-512.png',
  'icons/apple-touch-icon.png',
  'vendor/katex/LICENSE',
  'vendor/katex/fonts/KaTeX_AMS-Regular.woff2',
  'vendor/katex/fonts/KaTeX_Caligraphic-Bold.woff2',
  'vendor/katex/fonts/KaTeX_Caligraphic-Regular.woff2',
  'vendor/katex/fonts/KaTeX_Fraktur-Bold.woff2',
  'vendor/katex/fonts/KaTeX_Fraktur-Regular.woff2',
  'vendor/katex/fonts/KaTeX_Main-Bold.woff2',
  'vendor/katex/fonts/KaTeX_Main-BoldItalic.woff2',
  'vendor/katex/fonts/KaTeX_Main-Italic.woff2',
  'vendor/katex/fonts/KaTeX_Main-Regular.woff2',
  'vendor/katex/fonts/KaTeX_Math-BoldItalic.woff2',
  'vendor/katex/fonts/KaTeX_Math-Italic.woff2',
  'vendor/katex/fonts/KaTeX_SansSerif-Bold.woff2',
  'vendor/katex/fonts/KaTeX_SansSerif-Italic.woff2',
  'vendor/katex/fonts/KaTeX_SansSerif-Regular.woff2',
  'vendor/katex/fonts/KaTeX_Script-Regular.woff2',
  'vendor/katex/fonts/KaTeX_Size1-Regular.woff2',
  'vendor/katex/fonts/KaTeX_Size2-Regular.woff2',
  'vendor/katex/fonts/KaTeX_Size3-Regular.woff2',
  'vendor/katex/fonts/KaTeX_Size4-Regular.woff2',
  'vendor/katex/fonts/KaTeX_Typewriter-Regular.woff2',
  'vendor/katex/katex.min.css',
  'vendor/katex/katex.min.js'
];

// 설치 즉시 전부 받아 둔다
self.addEventListener('install', function (e) {
  e.waitUntil(
    caches.open(CACHE)
      .then(function (c) { return c.addAll(ASSETS.concat(['./'])); })
      .then(function () { return self.skipWaiting(); })
  );
});

// 새 버전이 활성화되면 옛 캐시를 지운다
self.addEventListener('activate', function (e) {
  e.waitUntil(
    caches.keys()
      .then(function (keys) {
        return Promise.all(keys.map(function (k) {
          return (k !== CACHE && k.indexOf('daily-integral-') === 0) ? caches.delete(k) : null;
        }));
      })
      .then(function () { return self.clients.claim(); })
  );
});

// 캐시 우선. 네트워크는 뒤에서 조용히 갱신만 한다(stale-while-revalidate).
// 문제 은행이 통째로 정적 파일이라 이 전략이면 오프라인에서 기능이 하나도 빠지지 않는다.
self.addEventListener('fetch', function (e) {
  var req = e.request;
  if (req.method !== 'GET') return;
  var url = new URL(req.url);
  if (url.origin !== self.location.origin) return;

  e.respondWith(
    caches.open(CACHE).then(function (cache) {
      return cache.match(req).then(function (hit) {
        var net = fetch(req).then(function (res) {
          if (res && res.ok) cache.put(req, res.clone());
          return res;
        }).catch(function () { return null; });

        // 캐시에 있으면 바로 준다
        if (hit) return hit;

        // 없으면 네트워크를 기다리고, 그것도 안 되면 문서 요청은 첫 화면으로 돌린다
        return net.then(function (res) {
          if (res) return res;
          if (req.mode === 'navigate') return cache.match('index.html');
          return new Response('', { status: 504, statusText: 'offline' });
        });
      });
    })
  );
});
