// --- Minimal Safe Service Worker ---

self.addEventListener("install", (event) => {
  console.log("Service Worker: Installed");
  self.skipWaiting();
});

self.addEventListener("activate", (event) => {
  console.log("Service Worker: Activated");
  clients.claim();
});

// ★ 全ての fetch をそのままネットに流す（キャッシュしない）
self.addEventListener("fetch", (event) => {
  return;
});
