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
  constructor(handler) {
    this.handler = handler;
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
    const v = this.eat("v");
    this.space();
    const symbols = [];
    do {
      symbols.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    this.eat("dot");
    this.dispatch([v, symbols]);
  }
  c() {
    const c = this.eat("c");
    this.space();
    const symbols = [];
    do {
      symbols.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    const dot = this.eat("dot");
    this.dispatch([c, symbols]);
  }
  dispatch(e) {
    if (this.handler) {
      this.handler.feed(e);
    }
  }
  d() {
    const d = this.eat("d");
    this.space();
    const symbols = [];
    do {
      symbols.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    this.eat("dot");
    this.dispatch([d, symbols]);
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
  f(label) {
    const f = this.eat("f");
    this.space();
    const type = this.eat("sequence");
    this.space();
    const varz = this.eat("sequence");
    this.space();
    this.eat("dot");
    this.dispatch([label, f, type, varz]);
  }
  e(label) {
    const e = this.eat("e");
    this.space();
    const varz = this.eat("sequence");
    this.space();
    const sequence = [];
    do {
      sequence.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    this.eat("dot");
    this.dispatch([label, e, varz, sequence]);
  }
  a(label) {
    const a = this.eat("a");
    this.space();
    const type = this.eat("sequence");
    this.space();
    const sequence = [];
    while (this.accepts("sequence")) {
      sequence.push(this.eat("sequence"));
      this.space();
    };
    this.eat("dot");
    this.dispatch([label, a, type, sequence]);
  }
  value() {
    return this.head.value.value;
  }
  compressed() {
    const p1 = this.eat("sequence"); // (
    this.space();
    const local = [];
    while (this.value() != ")") {
      local.push(this.eat("sequence"));
      this.space();
    };
    const p2 = this.eat("sequence"); // )
    this.space();
    const integers = [];
    do {
      integers.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    return [p1, local, p2, integers.join("")];
  }
  uncompressed() {
    const proof = [];
    do {
      proof.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    return proof;
  }
  proof() {
    const proof = this.eat("proof");
    this.space();
    if (this.value() == "(") {
      return [proof, this.compressed()];
    } else {
      return [proof, this.uncompressed()];
    }
  }
  p(label) {
    const p = this.eat("p");
    this.space();
    const type = this.eat("sequence");
    this.space();
    const sequence = [];
    do {
      sequence.push(this.eat("sequence"));
      this.space();
    } while (this.accepts("sequence"));
    const [proof, steps] = this.proof();
    this.eat("dot");
    this.dispatch([label, p, type, sequence, proof, steps]);
  }
  label() {
    const label = this.eat("sequence");
    this.space();
    if (this.accepts("f")) {
      this.f(label);
    } else if (this.accepts("e")) {
      this.e(label);
    } else if (this.accepts("a")) {
      this.a(label);
    } else if (this.accepts("p")) {
      this.p(label);
    } else {
      this.error();
    }
  }
  error() {
    throw new Error(`Syntax error: unexpected ${this.head.value.type} token.`);
  }
  block() {
    this.eat("lscope");
    this.dispatch("push");
    this.space();
    while (!this.accepts("rscope")) {
      this.statement();
      this.space(true);
    }
    this.eat("rscope");
    this.dispatch("pop");
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

function parse(code, handler) {
  const parser = new Parser(handler);
  const stream = tokens(code);
  return parser.parse(stream);
}

module.exports = {
  parse: parse,
};
