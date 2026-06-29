# History
index.html | 滥用 xiaoce.fun/guessword 的 api 接口，用 AI 做的简单破解版 (A simple cracked [albituary date] version of xiaoce.fun/guessword)

2026/6/29 我们发现chaofan为api增加了时间和会员验证，现在不能选择未来时间，也不能选择过早的时间（会提示要会员）。当前API校验规则是可以免费访问今天和昨天；网页限制在今天一天，已经没有破解的必要了。

如有需求，可以在 F12 呼出的 console 内输入 await (await fetch("/api/v0/quiz/daily/GuessWord/guessV1?date=20260629&word=xxx", {
  credentials: "include"
})).text();
其中 date 可以改称当天日期或前一天的 yyyymmdd 格式，word 改为要猜的单词。
