const moo = require("moo");

const lexicon = {
  comment: {match: /\$\([\s]+(?:(?!\$\))[\s\S])*\$\)/, lineBreaks: true},
  lfile: "$[",
  rfile: "$]",
  v: "$v",
  d: "$d",
  c: "$c",
  f: "$f",
  a: "$a",
  e: "$e",
  p: "$p",
  proof: "$=",
  dot: "$.",
  // question: "?",
  lscope: "${",
  rscope: "$}",
  //lparen: "(",
  //rparen: ")",
  ws: {match: /[\s]+/, lineBreaks: true},
  sequence: /[!-#%-~\?]+/,
  // letter_or_digit: /[A-Za-z0-9]/,
  // symbol: /[!-#%-~]+/,
};

const lexer = moo.compile(lexicon);

module.exports = {
  lexicon: lexicon,
  lexer: lexer
};
