# [rev] promise

1. 配布 `promise.js` を [de4js | JavaScript Deobfuscator and Unpacker](https://lelinhtinh.github.io/de4js/) で難読化解除します(この問題の場合はいい感じに改行してくれます)。その結果が[promise_deobfuscated.js](promise_deobfuscated.js)です。
2. [convert_promise_js.py](convert_promise_js.py)を実行し、シンボリック実行させるように変換します。変換結果が[promise_converted.js](promise_converted.js)です。
3. 変換結果を `promise.js` へ差し替えてから、配布 `index.html` を開いて実行させます。
4. `console.log` 結果にPythonコードがあるのでコピーして保存します。その結果が[console_log_output_solver.py](console_log_output_solver.py)です。
5. `console_log_output_solver.py`を実行してフラグを求めます。 
