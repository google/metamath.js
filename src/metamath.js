class Frame {
  constructor() {
    this.c = new Set();
    this.v = new Set();
    this.d = new Set();
    this.f = [];
    this.f_labels = {};
    this.e = [];
    this.e_labels = {};
  }
}
  
class Stack {
  constructor() {
    this.stack = [];
  }
    
  push() {
    const top = new Frame();
    this.stack.push(top);
    return top;
  }

  pop() {
    return this.stack.pop();
  }

  top() {
    return this.stack[this.stack.length - 1];
  }
    
  addC(tok) {
    const frame = this.top();
    
    if (frame.c.has(tok)) {
      throw new Error("const already declared in scope");
    }
    
    if (frame.v.has(tok)) {
      throw new Error("const already declared as a var in scope");
    }
    
    frame.c.add(tok);
  }

  addV(tok) {
    const frame = this.top();
    
    if (frame.v.has(tok)) {
      throw new Error("var already declared in scope");
    }
    
    if (frame.c.has(tok)) {
      throw new Error("var already declared as a const in scope");
    }
    
    frame.v.add(tok);
  }
  
  lookupV(tok) {
    for (const frame of [...this.stack].reverse()) {
      if (frame.v.has(tok)) {
        return true;
      }
    }
    return false;
  }
  
  lookupC(tok) {
    for (const frame of [...this.stack].reverse()) {
      if (frame.c.has(tok)) {
        return true;
      }
    }
    return false;
  }
  
  addF(varz, kind, label) {
    if (!this.lookupV(varz)) {
      throw new Error(`var "${varz}" in $f not defined.`);
    }
    if (!this.lookupC(kind)) {
      throw new Error(`const in $f not defined: ${kind}.`);
    }
    
    const frame = this.top();
    
    if (Object.keys(frame.f_labels).includes(varz)) {
      throw new Error(`var ${varz} in $f already defined in scope`);
    }

    // console.log(label);
    
    frame.f.push([varz, kind]);
    frame.f_labels[varz] = label;
  }
    
  addE(rule, kind, label) {
    const frame = this.top();
    frame.e.push([rule, kind, label]);
    const tag = [rule, kind].flat().join("");
    frame.e_labels[tag] = label;
  }

  addD([d, vars]) {
    const frame = this.top();
    if (vars.length < 2) {
      throw new Error(`Invalid disjoinet statement: neet at least two variables.`);
    }

    const declared = (variable) => {
      for (const frame of [...this.stack].reverse()) {
        if (frame.v.has(variable)) {
          return true;
        }
      }
      return false;
    }
    
    for (const variable of vars) {
      if (!declared(variable)) {
        throw new Error(`Disjoint statement of undeclared variable ${variable}.`);
      }
    }

    const contains = (pair) => {
      for (const prior of frame.d) {
        if (prior[0] == pair[0] && prior[1] == pair[1]) {
          return true;
        }
      }
      return false;
    }
    
    for (let i = 0; i < vars.length; i++) {
      for (let j = i + 1; j < vars.length; j++) {
        const pair = [vars[i], vars[j]];
        if (!contains(pair)) {
          frame.d.add(pair);
        }
      }
    }
  }

  lookupF(varz) {
    for (const frame of [...this.stack].reverse()) {
      if (frame.f_labels[varz]) {
        return frame.f_labels[varz];
      }
    }
    throw new Error(`Unknown $f key: ${varz}.`);
  }

  lookupE(rule, kind) {
    const tag = [rule, kind].flat().join("");
    for (const frame of [...this.stack].reverse()) {
      if (frame.e_labels[tag]) {
        return frame.e_labels[tag];
      }
    }        
    throw new Error(`Unknown $e key: ${tag}.`);
  }

  assert(type, rule) {
    const frame = this.top();
    const e = this.stack
          .map((frame) => frame.e)
          .flat();
    
    const mandatory = new Set();

    for (const [hyp] of [...e, [rule, type]]) {
      for (const tok of hyp) {
        if (this.lookupV(tok)) {
          mandatory.add(tok);
        }
      }
    }

    const dvs = [];
    for (const {d} of [...this.stack].reverse()) {
      for (const pair of d) {
        const [x, y] = pair;
        // If any of the disjoined variables declarations
        // refer to the mandatory variables, add that
        // condition to the assertion.
        if (mandatory.has(x) && mandatory.has(y)) {
          dvs.push(pair);
        }
      }
    }
      
    const f = [];

    for (const frame of [...this.stack].reverse()) {
      for (const [v, k, label] of [...frame.f].reverse()) {
        if (mandatory.has(v)) {
          f.unshift([k, v]);
          mandatory.delete(v);
        }
      }
    }
    
    return [dvs, f, e, [type, rule]];
  }
}

class MM {
  constructor() {
    this.frames = new Stack();
    this.labels = {};
  }

  feed(statements) {
    for (const stmt of statements) {
      const [first, second] = stmt;
      if (first == "$c") {
        const [, vars] = stmt;
        for (const varz of vars) {
          this.frames.addC(varz);
        }
        this.labels["$c"] ||= [];
        this.labels["$c"].push(stmt);
      } else if (first == "$v") {
        const [, vars] = stmt;
        for (const varz of vars) {
          this.frames.addV(varz);
        }
        this.labels["$v"] ||= [];
        this.labels["$v"].push(stmt);
      } else if (first == "${") {
        const [p, inner, q] = stmt;
        this.read(inner);
      } else if (second == "$f") {
        const [label, f, type, variable] = stmt;
        this.frames.addF(variable, type, label);
        this.labels[label] = [f, [type, variable]];
      } else if (first == "$d") {
        this.frames.addD(stmt);
      } else if (second == "$a") {
        const [label, a, type, rule] = stmt;
        const axiom = this.frames.assert(type, rule);
        ///if (label == "ax-mp") {
        // console.log(stmt);
        //console.log(axiom);          
        //throw new Error("hi");
        //}
        this.labels[label] = [a, axiom];
      } else if (second == "$e") {
        const [label, e, type, rule] = stmt;
        this.frames.addE(rule, type, label);
        this.labels[label] = [e, [type, rule]];
      } else if (second == "$p") {
        const [label, p, type, theorem, d, proof] = stmt;
        //try {
        const result = this.verify(label, type, theorem, proof);
        this.labels[label] = [p, this.frames.assert(type, theorem), result];
        //} catch (e) {
        //  console.log(e);
        //  throw e;
        //}
      } else {
        throw new Error(`Unknown statement type: ${stmt}.`);
      }
    }
  }
  
  read(statements) {
    this.frames.push();
    this.feed(statements);
    return this.frames.pop();
  }

  // Algorithms from:
  // https://us.metamath.org/downloads/metamath.pdf
  // https://mm.ivank.net/js/MM.js
  // https://github.com/david-a-wheeler/mmverify.py/blob/master/mmverify.py
  decompress(type, theorem, proof) {
    const [d, f, e] = this.frames.assert(type, theorem);

    const labels = [];

    const args = f
          .map(([k, v]) => v)
          .map((v) => this.frames.lookupF(v));
    
    const hyps = e
          .map(([rule, type]) => this.frames.lookupE(rule, type));
    labels.push(...args);
    labels.push(...hyps);

    //console.log(args);
    //console.log(hyps);
    
    const m = labels.length;

    const [l, local, r, compressed] = proof;
    
    const n = local.length;

    let integers = [];
    let current = 0;

    for (let ch of compressed) {
      if (ch >= 'A' && ch <= 'T') {
        // Shift the current integer left by 20 bits.
        // let result = ;
        // Add the next 20 bits as the least significant bits.
        //result += ch.charCodeAt(0) - 'A'.charCodeAt(0) + 1;
        const result = current * 20 + ch.charCodeAt(0) - 'A'.charCodeAt(0) + 1;
        integers.push(result);
        // Reset the current integer.
        current = 0;
        // throw new Error(ch);
      } else if (ch >= 'U' && ch < 'Y') {
        // Shift the current integer left by 5 bits.
        current = current * 5;
        // Add the next 5 bits as the last significant bits.
        current += ch.charCodeAt(0) - 'U'.charCodeAt(0) + 1;
      } else if (ch == 'Z') {
        integers.push(-1);
        // current = 0;
        // throw new Error(`Unsupported operation: marker while proving ${proof}.`);
      } else {
        throw new Error(`Unexpected character "${ch}" in compressed proof`);
      }
    }

    //console.log(`compressed: ${compressed}.`);
    //console.log(`integers: ${integers}`);
    const result = [];
    const saved = [];
    let total_saved = 0;
    for (const integer of integers) {
      if (integer == -1) {
        const last = result[result.length - 1];
        const [type, [dvs, f, e]] = this.labels[last];
        // pushes the last step
        saved.push(result.slice(result.length - 1 - (f.length + e.length), result.length));
        // saved.push(last);
        // console.log(result);
        // saved.push([...result]);
        total_saved++;
        // throw new Error("Marker!");
      } else if (integer > 0 && integer <= m) {
        // throw new Error("hi");
        result.push(labels[integer - 1]);
      } else if (integer > m && integer <= (m + n)) {
        const i = integer - m;
        result.push(local[i - 1]);
      } else if (integer > (m + n) && integer <= (m + n + total_saved)) {
        //const stmt = saved[integer - m];
        //console.log(proof);
        // console.log(`integer=${integer} m=${m} n=${n} saved=${saved.length}`);
        // console.log(`${integer - m}`);
        // console.log(labels[integer - m]);
        //console.log(`labels=${labels} local=${local}`);
        //console.log(`integer=${integer} m=${m} n=${n} saved=${saved.length} total=${total_saved}`);
        //console.log(integer);
        //console.log(stmt);
        //console.log(`saved: ${saved[integer - (m + n) - 1]}`);
        // Interestinly, David treats this step repetition as an axiom
        // because it has already been proven, so there is no point in
        // re-doing it:
        // https://github.com/david-a-wheeler/mmverify.py/blob/master/mmverify.py
        // Where as Ivan, unrolls the entire dependency tree and reproves it:
        // https://mm.ivank.net/js/MM.js
        // const step = saved[integer - (m + n) - 1];
        //console.log(this.labels[step]);
        // const [type, [dvs, f, e]] = this.labels[step];
        //console.log(f);
        // console.log(e);
        //throw new Error(`hi`);
        result.push(...saved[integer - (m + n) - 1]);
        // throw new Error(`Reference!`);
      } else {
        console.log(`integer=${integer} m=${m} n=${n} saved=${saved.length}`);
        throw new Error(`Invalid integer number "${integer}" in compressed proof.`);
      }
    }

    // console.log(result);
    
    return result;
  }
    
  verify(label, type, theorem, proof) {
    if (proof[0] == "(") {
      proof = this.decompress(type, theorem, proof);
    }

    const stack = [];

    const steps = [];

    let index = 0;
    for (const step of proof) {
      if (!this.labels[step]) {
        throw new Error(`Unknown theorem "${step}" in the proof for "${label}".`);
      }
      const [op, data] = this.labels[step];
      if (op == "$e" || op == "$f") {
        const [type, varz] = data;
        stack.push([index, type, [varz]]);
        const t = stack[stack.length - 1];
        steps.push([step, [t[1], t[2]], []]);
      } else if (op == "$a" || op == "$p") {
        const [dvs, mandatory, hyp, result] = data;
        const subs = {};
        const npop = mandatory.length + hyp.length;
        const base = stack.length - npop;
        // console.log(`Stack: base=${base}, npop=${npop}, length=${stack.length}`);
        const args = [];
        let sp = base;
        if (sp < 0) {
          throw new Error(`Empty stack ${sp}.`);
        }
        
        for (const [k, v] of mandatory) {
          const top = stack[sp];
          if (top[1] != k) {
            console.log(`Stack at ${sp} because ${mandatory.length} args + ${hyp.length} hypothesis:`);
            for (let [index, type, string] of stack.reverse()) {
              console.log(`  ${type} ${string.join("")}`);
            }
            console.log(mandatory);
            throw new Error(`Step ${step} of ${label}: argument type of ${v} doesn't match with the top of the stack. Expected ${k} but got ${top[1]}.`);
          }
          subs[v] = top[2];
          args.push(top[0]);
          sp++;
        }
        
        for (const [h, type] of hyp) {
          const top = stack[sp];
          if (top[1] != type) {
            throw new Error(`Step ${step}: argument type doesn't match with the topf of the stack. Expected ${type} but got ${top[0]}.`);
          }
          
          const sub = h
                .map((tok) => subs[tok] ? subs[tok] : tok);
          if (top[2].flat().join("") != sub.flat().join("")) {
            throw new Error(`Step ${step}: argument value for substitution ${JSON.stringify(subs)} of the hypothesis ${h.join(" ")} doesn't match with the top of the stack. Expected ${sub.flat().join(" ")} but got ${top[1].join(" ")}.`);
          }
          args.push(top[0]);
          sp++;
        }

        // Page 133: Verifying Disjoint Variable Restrictions
        // https://us.metamath.org/downloads/metamath.pdf
        // Each substitution made in a proof must be checked to verify that any disjoint
        // variable restrictions are satisfied, as follows.
        // If two variables replaced by a substitution exist in a mandatory $d
        // statement of the assertion referenced, the two expressions resulting from the
        // substitution must satisfy the following conditions. First, the two expressions
        // must have no variables in common. Second, each possible pair of variables,
        // one from each expression, must exist in an active $d statement of the $p
        // statement containing the proof.
        for (const [x, y] of dvs) {
          throw new Error(`Unsupported disjoint variable restriction`);
        }
        
        stack.splice(base, npop);
        
        const el = result[1]
              .map((tok) => subs[tok] ? subs[tok] : tok);

        stack.push([index, result[0], el.flat()]);
        const t = stack[stack.length - 1];
        steps.push([step, [t[1], t[2]], args]);
      }

      index++;
    }

    if (stack.length != 1) {
      throw new Error(`Stack has more than one entry left`);
    }
    
    const [, kind, last] = stack.pop();

    if (type != kind) {
      throw new Error(`Assertion proved doesn't match: expected ${type} but got ${kind}`);
    }
    
    if (last.join(" ") != theorem.join(" ")) {
      throw new Error(`Assertion proved doesn't match: expected ${theorem.join("")} but got ${last.join("")}`);
    }

    return steps;
  }
}


module.exports = {
  Frame: Frame,
  Stack: Stack,
  MM: MM
};
