# [misc] toybox

1. 配布コードを読むと、`server.c` で `FILE *fp = fopen("flag.txt", "r");` したまま閉じてないことが分かります。そのまま `execl` などして提供ELFが実行されているため、 `flag.txt` のfdがの降り続けています。
2. 「fdを検索してファイルとして開いていそうな内容を出力する」コードを書きます。それが[solve.s](solve.s)です。
3. `gcc -nostdlib -static solve.s` でコンパイルしたELFを提出して実行させます。フラグが表示されます。
