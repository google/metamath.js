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
    
    frame.f.push([varz, kind]);
    frame.f_labels[varz] = label;
  }
    
  addE(rule, kind, label) {
    const frame = this.top();
    frame.e.push([rule, kind]);
    const tag = [rule, kind].flat().join("");
    frame.e_labels[tag] = label;
  }

  addD(stat) {
    const frame = this.top();
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
      // console.log(hyp);
      for (const tok of hyp) {
        if (this.lookupV(tok)) {
          mandatory.add(tok);
        }
      }
    }

    // TODO: deal with distinct variables.
    const dvs = [];
      
    const f = [];

    // console.log(mandatory);
    for (const frame of [...this.stack].reverse()) {
      for (const [v, k] of [...frame.f].reverse()) {
        // console.log(`${v} ${k}`);
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
  
  read(block) {
    this.frames.push();
    for (const stmt of block) {
      const [first, second] = stmt;
      if (first == "$c") {
        const [, vars] = stmt;
        for (const varz of vars) {
          this.frames.addC(varz);
        }
      } else if (first == "$v") {
        const [, vars] = stmt;
        for (const varz of vars) {
          this.frames.addV(varz);
        }
      } else if (first == "${") {
        const [p, inner, q] = stmt;
        this.read(inner);
      } else if (second == "$f") {
        const [label, f, type, variable] = stmt;
        this.frames.addF(variable, type, label);
        this.labels[label] = [f, [type, variable]];
      } else if (second == "$d") {
        throw new Error(`Unsupported statement type $d.`);
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
        const result = this.verify(label, type, theorem, proof);
        this.labels[label] = [p, this.frames.assert(type, theorem), result];
      } else {
        throw new Error(`Unknown statement type: ${stmt}.`);
      }
    }
    
    return this.frames.pop();
  }

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
    
    const m = labels.length;

    const [l, local, r, compressed] = proof;
    
    const n = local.length;

    let integers = [];
    let current = 0;

    for (let ch of compressed) {
      if (ch >= 'A' && ch <= 'T') {
        // Shift the current integer left by 20 bits.
        let result = current * 20;
        // Add the next 20 bits as the least significant bits.
        result += ch.charCodeAt(0) - 'A'.charCodeAt(0) + 1;
        integers.push(result);
        // Reset the current integer.
        current = 0;
        // throw new Error(ch);
      } else if (ch >= 'U' && ch < 'Y') {
        // Shift the current integer left by 5 bits.
        current = current * 5;
        // Add the next 5 bits as the last significant bits.
        current += ch.charCodeAt(0) - 'A'.charCodeAt(0) + 1;
      } else if (ch == 'Z') {
        throw new Error("marker");
      } else {
        throw new Error(`Unexpected character "${ch}" in compressed proof`);
      }
    }

    const result = [];
    for (const integer of integers) {
      if (integer > 0 && integer <= m) {
        result.push(labels[integer - 1]);
      } else if (integer > m && integer <= (m + n)) {
        const i = integer - m;
        result.push(local[i - 1]);
      } else {
        throw new Error(`Invalid integer number "${integer}" in compressed proof.`);
      }
    }
    
    return result;
  }
    
  verify(label, type, theorem, proof) {
    if (proof[0] == "(") {
      proof = this.decompress(type, theorem, proof);
    }

    // console.log(proof);
      
    const stack = [];
    for (const step of proof) {
      if (!this.labels[step]) {
        throw new Error(`Unknown theorem "${step}" in the proof for "${label}".`);
      }
      const [op, data] = this.labels[step];
      if (op == "$e" || op == "$f") {
        const [type, varz] = data;
        //console.log(`push ${op} ${step}: ${data.flat().join(" ")}`);
        //console.log(data);
        //throw new Error("hi");
        stack.push([type, [varz]]);
      } else if (op == "$a" || op == "$p") {
        const [dist, mandatory, hyp, result] = data;
        const subs = {};
        //console.log(`call ${op} ${step}: ${mandatory.length} args and ${hyp.length} logical`);
        //console.log(`Stack:`);
        //for (let entry of [...stack].reverse()) {
        //  console.log(`- [${entry.flat().join(" ")}]`);
        //}

        const npop = mandatory.length + hyp.length;
        const base = stack.length - npop;
        let sp = base;
        //console.log(`base (${base}) = top (${stack.length}) - (${npop})`);
        //console.log(stack[sp]);
        if (sp < 0) {
          throw new Error(`Empty stack ${sp}.`);
        }
        
        for (const [k, v] of mandatory) {
          const top = stack[sp];
          // console.log(`- poping [${top.flat().join(" ")}]`);
          if (top[0] != k) {
            throw new Error(`Step ${step}: argument types don't match. Expected ${k} but got ${top[0]}.`);
          }
          subs[v] = top[1];
          sp++;
        }
        
        // console.log(hyp);
        
        // TODO: go through the logical hypothesis.
        //console.log(subs);
        //console.log(hyp);
        for (const [h, type] of hyp) {
          const top = stack[sp];
          //console.log(`- poping [${top.flat().join(" ")}]`);
          if (top[0] != type) {
            throw new Error(`Step ${step}: argument types don't match. Expected ${type} but got ${top[0]}.`);
          }
          
          const sub = h
                .map((tok) => subs[tok] ? subs[tok] : tok);
          // console.log(top[1]);
          if (top[1].flat().join("") != sub.flat().join("")) {
            //console.log(top[1]);
            //console.log(sub);
            throw new Error(`Step ${step}: argument values don't match. Expected ${sub} but got ${top[1]}.`);
          }
          sp++;
          // throw new Error("Need to go through the logical hypothesis");
        }

        stack.splice(base, npop);
        // console.log(sp);
        
        const el = result[1]
              .map((tok) => subs[tok] ? subs[tok] : tok);

        // console.log(el);
        //console.log(`... and pushing ${result[0]} ${el.flat().join(" ")}`);
        
        stack.push([result[0], el.flat()]);

        //console.log(`Stack:`);
        //for (let entry of [...stack].reverse()) {
        //  console.log(`- [${entry.flat().join(" ")}]`);
        //}

        // throw new Error("hi");


      }
    }

    if (stack.length != 1) {
      throw new Error(`Stack has more than one entry left`);
    }
    
    const [, last] = stack.pop();
    
    if (last.join("") != theorem.join("")) {
      throw new Error(`Assertion proved doesn't match: ${last.join("")} != ${theorem.join("")}`);
    }
    
    return proof;
  }
}


module.exports = {
  Frame: Frame,
  Stack: Stack,
  MM: MM
};
