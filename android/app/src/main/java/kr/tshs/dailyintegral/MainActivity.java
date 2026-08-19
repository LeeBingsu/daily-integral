package kr.tshs.dailyintegral;

import android.annotation.SuppressLint;
import android.graphics.Color;
import android.os.Bundle;
import android.webkit.ValueCallback;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.Toast;

import androidx.activity.OnBackPressedCallback;
import androidx.appcompat.app.AppCompatActivity;
import androidx.webkit.WebViewAssetLoader;

/**
 * 웹뷰 껍데기. 문제 은행·채점·기록이 전부 자바스크립트 안에서 돌아가므로
 * 자산을 APK 에 넣어 두면 설치 직후부터 네트워크 없이 그대로 쓸 수 있다.
 *
 * file:// 대신 WebViewAssetLoader 로 https 출처를 만들어 준다.
 * file:// 출처에서는 localStorage 가 막히는 기기가 있어서, 기록이 날아가는 걸 막으려는 것.
 */
public class MainActivity extends AppCompatActivity {

    private WebView web;
    private long lastBackAt;

    @SuppressLint("SetJavaScriptEnabled")
    @Override
    protected void onCreate(Bundle saved) {
        super.onCreate(saved);

        final WebViewAssetLoader loader = new WebViewAssetLoader.Builder()
                .addPathHandler("/assets/", new WebViewAssetLoader.AssetsPathHandler(this))
                .build();

        web = new WebView(this);
        web.setBackgroundColor(Color.parseColor("#eef2f7"));

        WebSettings s = web.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);          // localStorage — 기록이 여기 쌓인다
        s.setAllowFileAccess(false);
        s.setAllowContentAccess(false);
        s.setCacheMode(WebSettings.LOAD_NO_CACHE);   // 자산이 APK 안에 있으니 캐시가 필요 없다

        web.setWebViewClient(new WebViewClient() {
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView v, WebResourceRequest req) {
                return loader.shouldInterceptRequest(req.getUrl());
            }

            @Override
            public boolean shouldOverrideUrlLoading(WebView v, WebResourceRequest req) {
                // 앱 자산 밖으로 나가는 링크는 웹뷰에서 열지 않는다
                return !"appassets.androidplatform.net".equals(req.getUrl().getHost());
            }
        });

        setContentView(web);

        if (saved != null) web.restoreState(saved);
        else web.loadUrl("https://appassets.androidplatform.net/assets/index.html");

        /*
         * 뒤로 가기.
         *
         *   한 페이지 안에서 화면만 갈아 끼우는 사이트라 웹뷰가 보기엔 방문 기록이
         *   하나뿐이다. 그래서 예전에는 어느 화면에서 눌러도 앱이 바로 닫혔다.
         *   웹 쪽 appBack() 에 '한 단계 뒤'가 있는지 먼저 물어보고,
         *   있다고 하면(연습장이 열려 있거나 첫 화면이 아니면) 앱을 닫지 않는다.
         *   첫 화면에서는 두 번 눌러야 닫히게 해 실수로 나가는 걸 막는다.
         */
        final OnBackPressedCallback back = new OnBackPressedCallback(true) {
            @Override
            public void handleOnBackPressed() {
                final OnBackPressedCallback self = this;
                web.evaluateJavascript(
                        "(function(){try{return window.appBack&&window.appBack()?1:0}catch(e){return 0}})()",
                        new ValueCallback<String>() {
                            @Override
                            public void onReceiveValue(String v) {
                                if ("1".equals(v)) return;       // 웹이 처리했다
                                if (web.canGoBack()) { web.goBack(); return; }

                                long now = System.currentTimeMillis();
                                if (now - lastBackAt < 2000) {
                                    self.setEnabled(false);
                                    getOnBackPressedDispatcher().onBackPressed();
                                    return;
                                }
                                lastBackAt = now;
                                Toast.makeText(MainActivity.this, R.string.back_to_exit,
                                        Toast.LENGTH_SHORT).show();
                            }
                        });
            }
        };
        getOnBackPressedDispatcher().addCallback(this, back);
    }

    @Override
    protected void onSaveInstanceState(Bundle out) {
        super.onSaveInstanceState(out);
        web.saveState(out);
    }
}
