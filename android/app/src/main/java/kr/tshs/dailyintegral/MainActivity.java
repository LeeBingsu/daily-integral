package kr.tshs.dailyintegral;

import android.annotation.SuppressLint;
import android.graphics.Color;
import android.os.Bundle;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;

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

        // 뒤로 가기는 웹 히스토리를 먼저 따라간다
        getOnBackPressedDispatcher().addCallback(this, new OnBackPressedCallback(true) {
            @Override
            public void handleOnBackPressed() {
                if (web.canGoBack()) web.goBack();
                else {
                    setEnabled(false);
                    getOnBackPressedDispatcher().onBackPressed();
                }
            }
        });
    }

    @Override
    protected void onSaveInstanceState(Bundle out) {
        super.onSaveInstanceState(out);
        web.saveState(out);
    }
}
