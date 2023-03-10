const moo = require("moo");
const {MM, Compressor} = require("./metamath.js");

class Lexer {
  constructor() {
    const lexicon = {
      ["comment-expr"]: {match: /\/\*\*.*\*\//, lineBreaks: true},
      ["comment"]: {match: /\/\/.*\n/, lineBreaks: true},
      ["ws"]: {match: /[\s]+/, lineBreaks: true},
      ["_include_"]: "include",
      //["const"]: "const",
      //["var"]: "var",
      ["theorem"]: "theorem",
      ["axiom"]: "axiom",
      ["proof"]: "proof",
      ["end"]: "end",
      ["let"]: "let",
      ["step"]: "step",
      ["assume"]: "assume",
      ["disjoint"]: "disjoint",
      ["assert"]: "assert",
      ["("]: "(",
      [")"]: ")",
      ['"']: '"',
      [":"]: ":",
      [","]: ",",
      [";"]: ";",
      ["@"]: "@",
      ["#"]: "#",
      ["label"]: /[A-Za-z0-9-_.]+/,
      ["sequence"]: /[!-#%-~\?]+/,
    };
    this.lexer = moo.compile(lexicon);
  }
  parse(code) {
    this.lexer.reset(code);
  }
  next() {
    let next = this.lexer.next();
    if (!next) {
      this.head = undefined;
      return;
    }
    let {type, text} = next;
    this.head = [type, text];
    return this.head;
  }
  done() {
    assertThat(this.lexer.next()).equalsTo(undefined);
  }
  ws() {
    assertThat(this.next()[0]).equalsTo("ws");
  }
  eat(type, value) {
    assertThat(this.next()).equalsTo([type, value ? value : type]);
  };
}

function assertThat(a) {
  return {
    equalsTo(b) {
      if (JSON.stringify(a) != JSON.stringify(b)) {
        throw new Error(`Assertion error: ${a} != ${b}.`);
      }
    }
  };
}


const symbols = [
  // a subset of possible symbols
  "label",
  // reserved keywords that can also be symbols
  '"',
  "(",
  ")",
  ",",
  ":",
  ";",
  "@",
  "#",
  "//",
  // catch all types of sequences
  "sequence",
];

const labels = [
  // a subset of possible labels
  "label",
  // reserved keywords that can also be labels
  "_include_",
  // "const",
  // "var",
  "theorem",
  "axiom",
  "proof",
  //"end",
  "let",
  "step",
  "assume",
  "disjoint",
  "assert",
  // catch all types of sequences
];

class Parser {
  constructor() {
    this.lexer = new Lexer();
  }
  parse(code) {
    this.lexer.parse(code);
    return this.top();
  }
  eat(...types) {
    if (!this.lexer.head) {
      this.error();
    }
    for (let type of types) {
      if (this.lexer.head[0] == type) {
        const value = this.lexer.head[1];
        this.lexer.next();
        return value;
      }
    }
    this.error();
  }
  error() {
    const {head} = this.lexer;
    const {line, col} = this.lexer.lexer;
    throw new Error(`Unexpected token "${head[1]}" (${head[0]}) on line ${line} column ${col}.`);
  }
  
  accepts(...types) {
    if (!this.lexer.head) {
      return false;
    }
    for (let type of types) {
      if (this.lexer.head[0] == type) {
        return true;
      }
    }
    return false;
  }
  
  ws(optional = false) {
    const sp = ["ws", "comment", "comment-expr"];
    // const sp = ["ws"];
    if (this.accepts(...sp)) {
      this.eat(...sp);
      // allows multiple whitespace types intermingled
      while (this.accepts(...sp)) {
        this.eat(...sp);
      }
    } else if (!optional) {
      this.error();
    }
  }

  declaration(type, label = true, multiple = true, empty = true) {
    const result = [];
    this.eat(type);
    this.ws();
    if (label) {
      result.push(this. label());
      this.ws(true);
      this.eat(":");
      this.ws(true);
    }
    let first = this.symbol();
    result.push(first);
    this.ws(false);
    if (!this.accepts(...symbols) && empty) {
      // If empty symbols are allowed
      result.push("");
      return [type, result];
    }
    let second = this.symbol();
    //console.log(second);
    result.push(second);
    this.ws(false);
    if (multiple) {
      while (this.accepts(...symbols)) {
        result.push(this.symbol());
        this.ws(false);
      };
    }
    return [type, result];
  }

  axiom() {
    this.eat("axiom");
    this.ws();
    let name = this.label();
    this.ws();
    let h = this.header();
    this.eat("end");
    this.ws();
    return ["axiom", name, h];
  }
  
  header() {
    this.ws(true);
    let lets = [];
    while (this.accepts("let")) {
      lets.push(this.declaration("let", true, false));
    }
    
    this.ws(true);
    let ifs = [];
    while (this.accepts("assume")) {
      ifs.push(this.declaration("assume", true, true));
    }
    
    this.ws(true);
    let disjoints = [];
    while (this.accepts("disjoint")) {
      disjoints.push(this.declaration("disjoint", false, true));
    }
    
    this.ws(true);
    let then = this.declaration("assert", false, true);
    return [lets, ifs, disjoints, then];
  }

  args() {
    this.eat("(");
    this.ws(true);
    let args = [];
    if (this.accepts(...labels)) {
      args.push(this.label());
      this.ws(true);
    }
    while (this.accepts(",")) {
      this.eat(",");
      this.ws(true);
      args.push(this.label());
    }
    this.ws(true);
    this.eat(")");
    return args;
  }
  
  step() {
    const result = [];
    this.eat("step");
    this.eat("ws");
    // index
    result.push(this.label());
    this.ws(true);
    this.eat(")");
    this.ws(true);
    // a step can either be ...
    if (this.accepts("#")) {
      // ... a marker ...
      result.push(this.eat("#"));
    } else if (this.accepts("@")) {
      // ... a recall ...
      result.push(this.eat("@"));
      result.push(this.label());
    } else {
      // ... or call.
      result.push(this.label());
      result.push(this.args());
    }
    this.ws(true);
    this.eat(":");
    this.ws(true);
    let sequence = [];
    result.push(sequence);
    while (this.accepts(...symbols)) {
      sequence.push(this.symbol());
      this.ws(true);
    }
    return result;
  }

  symbol() {
    let name = this.eat(...symbols);
    while (this.accepts(...symbols)) {
      name += this.eat(...symbols);
    }
    return name;
  }
  
  label() {
    let name = this.eat(...labels);
    while (this.accepts(...labels)) {
      name += this.eat(...labels);
    }
    return name;
  }
  
  theorem() {
    this.eat("theorem");
    this.ws();

    let name = this.label();
    this.ws();
    let head = this.header();

    this.ws(true);
    this.eat("proof");
    this.ws(true);
    
    let steps = [];
    do {
      if (this.accepts(...labels)) {
        steps.push(this.label());
      } else if (this.accepts("#")) {
        steps.push(this.eat("#"));
      } else if (this.accepts("@")) {
        steps.push(`${this.eat("@")}${this.label()}`);
      } else {
        break;
      }
      this.ws();
    } while (true);

    this.eat("end");
    this.ws();

    return ["theorem", name, head, steps];
  }
  
  include() {
    this.eat("_include_");
    this.ws();
    this.eat('"');
    const name = this.eat("label");
    this.eat('"');
    this.ws();
    return ["include", name];
  }
    
  top() {
    this.lexer.next();
    let result = [];
    do {
      if (this.accepts("ws")) {
        this.ws();
      } else if (this.accepts("//")) {
        throw new Error("hi");
      } else if (this.accepts("axiom")) {
        result.push(this.axiom());
      } else if (this.accepts("theorem")) {
        result.push(this.theorem());
      } else if (this.accepts("_include_")) {
        result.push(this.include());
      } else {
        this.error();
      }
      // console.log(this.lexer.head);
    } while (this.lexer.head);
    // throw new Error("hi");
    return result;
  }
}

class Compiler {
  constructor(loader) {
    this.load = loader;
  }
  async preprocess(dir, file) {
    const queue = [file];

    const files = {};
    
    while (queue.length > 0) {
      const head = queue.shift();

      const program = await this.load(`${dir}/${head}`);

      const parser = new Parser();
      const code = parser.parse(program.toString());

      files[head] = code;

      // Take all include statements that have never
      // been seen before and push them into the queue
      const include = code
            .filter(([type]) => type == "include")
            .map(([, name]) => name)
            .filter((name) => !files[name]);

      queue.push(...include);
    }

    return files;
  }

  async compile(dirOrSource, file) {
    if (!file) {
      let parser = new Parser();
      let code = parser.parse(dirOrSource);      
      return this.transpile(code);
    }
    const files = await this.preprocess(dirOrSource, file);
    const dump = Object.values(files)
          .flat()
          .filter(([type]) => type != "include");
    return this.transpile(dump);
  }

  transpile(code) {
    //console.log(code);
    //throw new Error();

    // console.log(code);
    
    const consts = new Set();
    for (let [type, label, [vars, assumes, disjoints, [, assert]], proof] of code) {
      // All variable types are constants
      for (let type of vars.map(([, [label, type, name]]) => type)) {
        consts.add(type);
      }

      const names = vars.map(([, [label, type, name]]) => name);

      // All symbols in logical hypothesis that aren't variables are constants
      const logical = [...assumes]
            .map(([, [type, ...symbols]]) => [type, symbols])
            .map(([type, symbols]) => symbols.filter((symbol) => !names.includes(symbol)))
            .flat();
      for (let symbol of logical) {
        consts.add(symbol);
      }
      // All symbols in assertions that aren't variables are constants
      for (let symbol of assert.filter((symbol) => !names.includes(symbol))) {
        consts.add(symbol);
      }
    }

    let result = [];
    result.push(`$c ${[...consts].join(" ")} $.`);

    for (let [type, label, [vars, assumes, disjoints, [, assert]], proof] of code) {
      const names = vars.map(([, [label, type, name]]) => name);
      const types = vars.map(([, [label, type, name]]) => `  ${label} $f ${type} ${name} $.`);
      const logical = [...assumes]
          .map(([, assumption]) => [assumption.shift(), assumption.shift(), assumption])
          .map(([label, type, symbols]) => `  ${label} $e ${type} ${symbols.join(" ")} $.`);
      
      const dvis = disjoints.map(([, vars]) => `${vars.join(" ")}`);
      
      const v = names.length > 0 ? `  $v ${names.join(" ")} $.` : "";
      const f = types.length > 0 ? `${types.join("\n")}` : "";
      const e = logical.length > 0 ? `${logical.join("\n")}` : "";
      const d = disjoints.length > 0 ? `  $d ${dvis.join(" ")} $.` : "";

      let p = "";

      if (proof) {
        let compress = false;
        const s = proof.map((label) => {
          if (label == "#") {
            compress = true;
            return -1;
          } else if (label.startsWith("@")) {
            return parseInt(label.substr(1));
          }
          return label;
        });

        if (!compress) {
          p = `$= ${proof.join(" ")} `;
        } else {
          const f = vars.map(([letty, [label]]) => label);
          const e = [...assumes]
                .map(([, assumption]) => [assumption.shift(), assumption.shift(), assumption])
                .map(([label, type, symbols]) => label);
          const compressor = new Compressor([...f, ...e], s);
          const compressed = compressor.compress();
          p = `$= ( ${compressor.external().join(" ")} ) ${compressor.compress()} `;
        }
      }
      
      result.push(`
$\{
${v}
${f}
${e}
${d}
  ${label} $${type == "axiom" ? "a" : "p"} ${assert.join(" ")} ${p}$.
$\}`);
    }

    return result.join("\n");
  }
}

class Transpiler {
  read(program) {
    this.mm = this.parse(program);
    return this;
  }

  closure(label) {
    const files = this.split();
    const queue = [label];

    const list = [];

    const result = {};
    
    while (queue.length > 0) {
      let head = queue.shift();
      if (list.includes(head)) {
        continue;
      }
      list.push(head);
      let [deps] = files[head];
      queue.push(...deps);
    }

    for (let file of list) {
      const [deps, content] = files[file];
      result[file] = [deps, content];
    }

    //console.log(result);
    //throw new Error("hi");
    
    return result;
  }
  
  dump() {
    let result = [];
    for (const [label] of Object.entries(this.mm.labels).filter(([, [type]]) => type == "$a")) {
      const [, code] = this.axiom(label);
      result.push(code);
    }
    for (const [label] of Object.entries(this.mm.labels).filter(([, [type]]) => type == "$p")) {
      const [, code] = this.theorem(label);
      result.push(code);
    }
    return result.join("");
  }
  
  axiom(label) {
    const [, [d, f, e, [type, axiom]]] = this.mm.labels[label];
    let args = f.map(([type, name, label]) => `  let ${label}: ${type} ${name}`).join("\n");
    if (Object.entries(f).length  > 0) {
      args += "\n";
    }
    
    let assumptions = e.map(([seq, type, name]) => `  assume ${name}: ${type} ${seq.join(" ")}`).join("\n");

    if (Object.entries(e).length > 0) {
      assumptions += "\n";
    }

    const result = `
axiom ${label}
${args}${assumptions}  assert ${type} ${axiom.join(' ')}
end
`;

    return [[], result];
  }

  theorem(label) {
    // const deps = [];
    const [, [d, f, e, [type, theorem]], func] = this.mm.labels[label];

    let args = f.map(([type, name, label]) => `  let ${label}: ${type} ${name}`).join("\n");

    //console.log();
    //throw new Error("hi");
    const local = [...f.map(([, , label]) => label),
                   ...e.map(([, , label]) => label)];

    // console.log(this.mm.frames.stack);
    const proof = func(undefined, true);
    
    const steps = proof.map(([step]) => step);
    // const compressed = new Compressor(local, steps).compress();
    //console.log(steps);
    //console.log(compressed);
    // throw new Error();
    const deps = [...new Set(steps)]
          .filter((step) => !local.includes(step) && typeof step != "number");
    
    let conds = "";
    
    let assumptions = e.map(([seq, type, name]) => `  assume ${name}: ${type} ${seq.join(" ")}`).join("\n");

    if (Object.entries(e).length > 0) {
      assumptions += "\n";
    }
    
    let diff = [];
    if (d.length > 0) {
      // throw new Error("unsupported distinguished variables operator");
      // args += " and (";
    }
    for (let [x, y] of d) {
      diff.push(`  disjoint ${x} ${y}`);
    }
    
    //if (d.length > 0) {
    //  args += "" + diff.join(", ") + ")";
    //}

    // console.log(proof);
    
    const body = proof.map(([step, [type, sequence = []], args = []], i) => {
      const call = typeof step == "number" ? (step == -1 ? `#` : `@${step}`) : `${step}`;
      return `    ${call}`;
    }).join("\n");
    
    const code = `
theorem ${label}
${args}
${assumptions}
${d.length > 0 ? diff.join("\n") : ""}
  assert ${type} ${theorem.join(' ')}

  proof
${body}
end
`;

    return [deps, code];
  }
  
  parse(program) {
    const mm = new MM();
    mm.push();
    
    const {parse} = require("../src/descent.js");
    parse(program.toString(), {
      feed(statement) {
        if (statement == "push") {
          mm.push();
        } else if (statement == "pop") {
          mm.pop();
        } else {
          mm.feed([statement]);
        }
      }
    });

    return mm;
  }
  
  split(program) {
    const result = {};
    
    for (const [label, value] of Object.entries(this.mm.labels)) {
      const [stmt] = value;
      if (stmt == "$e" || stmt == "$f" || label == "$c" || label == "$v") {
        continue;
      } else  if (stmt == "$a") {
        result[label] = this.axiom(label);
      } else if (stmt == "$p") {
        result[label] = this.theorem(label);
      } else {
        throw new Error(`Unknown statement type ${stmt}.`);
      }
    }
    return result;
  }
}

module.exports = {
  Lexer: Lexer,
  Parser: Parser,
  Compiler: Compiler,
  Transpiler: Transpiler,
};
