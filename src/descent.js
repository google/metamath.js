const {lexicon} = require("../src/lexer.js");
const moo = require("moo");

function *tokens(code) {
  const lexer = moo.compile(lexicon);
  lexer.reset(code);
  do {
    const next = lexer.next();
    if (!next) {
      return;
    }
    yield next;
  } while (true);
}

class Parser {
  constructor() {
  }
  parse(tokens) {
    this.it = tokens;
    this.head = this.it.next();
    return this.program();
  }
  eat(type) {
    if (this.head.value.type != type) {
      throw new Error(`Expected ${type} got ${this.head.value.type}.`);
    }
    const token = this.head.value;
    this.head = this.it.next();
    return token.value;
  }
  accepts(type) {
    if (this.done()) {
      return false;
    }
    if (this.head.value.type == type) {
      return true;
    }
    return false;
  }
  done() {
    return this.head.done;
  }
  ws() {
    this.eat("ws");
  }
  comment() {
    this.eat("comment");
  }
  v() {
    this.eat("v");
    this.space();
    do {
      this.eat("sequence");
      this.space();
    } while (this.accepts("sequence"));
    this.eat("dot");
  }
  c() {
    this.eat("c");
    this.space();
    do {
      this.eat("sequence");
      this.space();
    } while (this.accepts("sequence"));
    this.eat("dot");
  }
  d() {
    this.eat("d");
    this.space();
    do {
      this.eat("sequence");
      this.space();
    } while (this.accepts("sequence"));
    this.eat("dot");
  }
  space(optional = false) {
    do {
      if (this.accepts("ws")) {
        this.ws();
      } else if (this.accepts("comment")) {
        this.comment();
      } else if (!optional) {
        throw new Error(`Excepted a ws or a comment`);
      }
    } while (this.accepts("ws") || this.accepts("comment"));
  }
  f() {
    this.eat("f");
    this.space();
    this.eat("sequence");
    this.space();
    this.eat("sequence");
    this.space();
    this.eat("dot");
  }
  e() {
    this.eat("e");
    this.space();
    this.eat("sequence");
    this.space();
    do {
      this.eat("sequence");
      this.space();
    } while (this.accepts("sequence"));
    this.eat("dot");
  }
  a() {
    this.eat("a");
    this.space();
    this.eat("sequence");
    this.space();
    while (this.accepts("sequence")) {
      this.eat("sequence");
      this.space();
    };
    this.eat("dot");      
  }
  value() {
    return this.head.value.value;
  }
  compressed() {
    this.eat("sequence"); // (
    this.space();
    while (!this.value() == ")") {
      this.eat("sequence");
      this.space();
    };
    this.eat("sequence"); // )
    this.space();
    do {
      this.eat("sequence");
      this.space();
    } while (this.accepts("sequence"));
  }
  uncompressed() {
    do {
      this.eat("sequence");
      this.space();
    } while (this.accepts("sequence"));
  }
  proof() {
    this.eat("proof");
    this.space();
    if (this.value() == "(") {
      this.compressed();
    } else {
      this.uncompressed();
    }
  }
  p() {
    this.eat("p");
    this.space();
    this.eat("sequence");
    this.space();
    do {
      this.eat("sequence");
      this.space();
    } while (this.accepts("sequence"));
    this.proof();
    this.eat("dot");      
  }
  label() {
    const label = this.eat("sequence");
    this.space();
    if (this.accepts("f")) {
      this.f();
    } else if (this.accepts("e")) {
      this.e();
    } else if (this.accepts("a")) {
      this.a();
    } else if (this.accepts("p")) {
      // console.log(label);
      this.p();
    } else {
      this.error();
    }
  }
  error() {
    throw new Error(`Syntax error: unexpected ${this.head.value.type} token.`);
  }
  block() {
    this.eat("lscope");
    this.space();
    while (!this.accepts("rscope")) {
      this.statement();
      this.space(true);
    }
    this.eat("rscope");
  }
  file() {
    this.eat("lfile");
    this.space();
    this.eat("sequence");
    this.space();
    this.eat("rfile");
  }
  statement() {
    if (this.accepts("v")) {
      this.v();
    } else if (this.accepts("c")) {
      this.c();
    } else if (this.accepts("d")) {
      this.d();
    } else if (this.accepts("sequence")) {
      this.label();
    } else if (this.accepts("lscope")) {
      this.block();
    } else if (this.accepts("lfile")) {
      this.file();
    } else {
      this.error();
    }
  }
  program() {
    this.space(true);
    while (!this.done()) {
      this.statement();
      this.space(true);
    }
    return true;
  }
}

function parse(code) {
  const parser = new Parser();
  const stream = tokens(code);
  return parser.parse(stream);
}

module.exports = {
  parse: parse,
};
