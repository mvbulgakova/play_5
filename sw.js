// Офлайн-кэш «Пятого Постулата»: игра целиком работает без сети после первого запуска.
const V='p5-v1';
const FILES=['./','./index.html','./post.js','./portraits.js','./story.js','./font.js','./game.js','./manifest.webmanifest','./icons/icon.svg','./icons/icon-192.png','./icons/icon-512.png','./icons/apple-touch-icon.png'];
self.addEventListener('install',e=>{e.waitUntil(caches.open(V).then(c=>c.addAll(FILES)).then(()=>self.skipWaiting()));});
self.addEventListener('activate',e=>{e.waitUntil(caches.keys().then(ks=>Promise.all(ks.filter(k=>k!==V).map(k=>caches.delete(k)))).then(()=>self.clients.claim()));});
self.addEventListener('fetch',e=>{const r=e.request;if(r.method!=='GET')return;
  const u=new URL(r.url),local=u.origin===location.origin,fonts=/fonts\.(googleapis|gstatic)\.com$/.test(u.hostname);if(!local&&!fonts)return;
  // свои файлы: сначала сеть (чтобы обновления доходили), без сети — кэш; шрифты: сначала кэш
  e.respondWith(local?fetch(r).then(res=>{const c=res.clone();caches.open(V).then(k=>k.put(r,c));return res;}).catch(()=>caches.match(r,{ignoreSearch:true}))
    :caches.match(r).then(m=>m||fetch(r).then(res=>{const c=res.clone();caches.open(V).then(k=>k.put(r,c));return res;})));});
