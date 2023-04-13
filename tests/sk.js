const Assert = require("assert");

describe("S and K", async () => {
  it("S and K", async () => {
    const src = `
axiom term-k() {
  return term K;
}

axiom term-s() {
  return term S;
}

axiom term-c(term p, term q) {
  return term p [ q ];
}

axiom word-c(word w, word c) {
  return word w c;
}

axiom word-null() {
  return word $$;
}

axiom word-t(term x) {
  return word $x$;
}

axiom word-l() {
  return word [;
}

axiom word-r() {
  return word ];
}

// If Δ is a derivation ending in an expression of the form α((Kβ)γ)ι,
// then Δ followed by the term αβι is a derivation.
axiom ax-k(word head, term x, term y, word tail) {
  assume |- head K [ x ] [ y ] tail;
  return |- head x tail;
}

// If Δ is a derivation ending in an expression of the form α(((Sβ)γ)δ)ι,
// then Δ followed by the term α((βδ)(γδ))ι is a derivation.
axiom ax-s(word head, term x, term y, term z, word tail) {
  assume |- head S [ x ] [ y ] [ z ] tail;
  return |- head x [ z ] [ y [ z ] ] tail;
}

axiom df-eq(word head, term x, term y, word tail) {
  assume |- x = y;
  assume |- head x tail;
  return |- head y tail;
}

axiom df-sym(word head, term x, term y, word tail) {
  assume |- head x = y tail;
  return |- head y = x tail;
}

axiom df-id() {
  return |- I = S [ K ] [ K ];
}

axiom term-i() {
  return term I;
}

theorem id(
  id.fh: word head,
  id.f0: term x,
  id.ft: word tail) {

  assume id.e0: |- head I [ x ] tail;

  do {
    id.fh;
    id.f0;
    term-k;
    id.f0;
    term-c;
    id.ft;

      id.fh;
      term-k;
      term-k;
      id.f0;
      id.ft;

          id.fh;

          term-i;

          term-s;
          term-k;
          term-c;
          term-k;
          term-c;

          word-l;

          id.f0;
          word-t;
          word-c;

          word-r;
          word-c;

          id.ft;
          word-c;

          df-id;

          id.e0;

          df-eq;

      ax-s;

    ax-k;
  };

  return |- head x tail;
}

axiom term-f() {
  return term F;
}

axiom term-t() {
  return term T;
}

axiom df-true() {
  return |- T = K;
}

theorem true(
  true.h: word head,
  termx: term x,
  termy: term y,
  true.t: word tail) {

  assume true-e: |- head T [ x ] [ y ] tail;

  do {
    true.h;

    termx;

    termy;

    true.t;    

      true.h;

      term-t; // T

      term-k; // T K

      word-l; // T K [

      termx;  // T K [ x
      word-t; // T K [ x 
      word-c;

      word-r;
      word-c;

      word-l;
      word-c;

      termy;
      word-t;
      word-c;

      word-r;
      word-c;

      true.t;
      word-c;

      df-true;

      true-e;

      df-eq;  
    
   ax-k;
  };
  return |- head x tail;
}

axiom df-false() {
  return |- F = S [ K ];
}

theorem false(
  false.h: word head,
  termx: term x,
  termy: term y,
  false.t: word tail) {

  assume false-e: |- head F [ x ] [ y ] tail;

  do {

    false.h;
    termy;
    termx;
    termy;
    term-c;
    false.t;

      false.h;
      term-k;
      termx;
      termy;
      false.t;

        false.h; // head'

        term-f;  // x' = F

        term-s;  // S
        term-k;  // K
        term-c;  // y' = S [ K ]

        word-l;  // [

        termx;   // [ x
        word-t;  // [ x
        word-c;  // [ x

        word-r;  // [ x ]
        word-c;  // [ x ]

        word-l;  // [ x ] [
        word-c;  // [ x ] [

        termy;   // [ x ] [ y
        word-t;  // [ x ] [ y
        word-c;  // [ x ] [ y

        word-r;  // [ x ] [ y ]
        word-c;  // [ x ] [ y ]

        false.t; // tail
        word-c;  // tail' = [ x ] [ y ] tail

        df-false; // F = S [ K ]

        false-e;  // head F [ x ] [ y ] tail

        df-eq;  // head' y' tail' = head S [ K ] [ x ] [ y ] tail

      ax-s;

    ax-k;
  };

  return |- head y tail;
}

axiom term-not() {
  return term NOT;
}

axiom df-not() {
  return |- NOT = S [ S [ I ] [ K [ F ] ] ] [ K [ T ] ];
}

theorem not(
  not.h: word head,
  termx: term x,
  not.t: word tail) {

  assume not-e: |- head NOT [ x ] tail;

  do {

  // head x [ F ] [ K [ T ] [ x ] ] tail
  // Applying ax-k to get to:
  // head x [ F ] [ T ] tail

  // constructing head
  not.h;   // head

  termx;   // head x
  word-t;  // head x
  word-c;  // head x

  word-l;  // head x [
  word-c;  // head x [

  term-f;  // head x [ F
  word-t;  // head x [ F
  word-c;  // head x [ F

  word-r;  // head x [ F ]
  word-c;  // head x [ F ]

  word-l;  // head x [ F ] [
  word-c;  // head x [ F ] [

  term-t;  // x'''''' = T
  termx;   // y'''''' = x

  // constructing tail

  word-r;  // ]
  not.t;   // ] tail
  word-c;  // ] tail

    // head x [ K [ F ] [ x ] ] [ K [ T ] [ x ] ] tail
    // Applying ax-k to get to:
    // head x [ F ] [ K [ T ] [ x ] ] tail

    // constructing head
    not.h;   // head

    termx;   // head x
    word-t;  // head x
    word-c;  // head x

    word-l;  // head x [
    word-c;  // head x [

    term-f;  // x''''' = F
    termx; // y''''' = x

    // constructing tail
    word-r;  // ]
    word-l;  // ] [
    word-c;  // ] [

    term-k;  // ] [ K
    word-t;  // ] [ K
    word-c;  // ] [ K

    word-l;  // ] [ K [
    word-c;  // ] [ K [

    term-t;  // ] [ K [ T
    word-t;  // ] [ K [ T
    word-c;  // ] [ K [ T

    word-r;  // ] [ K [ T ]
    word-c;  // ] [ K [ T ]

    word-l;  // ] [ K [ T ] [
    word-c;  // ] [ K [ T ] [

    termx;   // ] [ K [ T ] [ x
    word-t;  // ] [ K [ T ] [ x
    word-c;  // ] [ K [ T ] [ x

    word-r;  // ] [ K [ T ] [ x ]
    word-c;  // ] [ K [ T ] [ x ]

    word-r;  // ] [ K [ T ] [ x ] ]
    word-c;  // ] [ K [ T ] [ x ] ]

    not.t; // tail
    word-c; // 
  

      // head I [ x ] [ K [ F ] [ x ] ] [ K [ T ] [ x ] ] tail 
      not.h;

      termx; // x'''' = x

      // constructing the tail [ K [ F ] [ x ] ] [ K [ T ] [ x ] ]

      word-l;  // [

      term-k;  // [ K
      word-t;  // [ K
      word-c;  // [ K

      word-l;  // [ K [
      word-c;  // [ K [

      term-f;  // [ K [ F
      word-t;  // [ K [ F
      word-c;  // [ K [ F

      word-r;  // [ K [ F ]
      word-c;  // [ K [ F ]
 
      word-l;  // [ K [ F ] [
      word-c;  // [ K [ F ] [

      termx;  // [ K [ F ] [ x
      word-t; // [ K [ F ] [ x
      word-c; // [ K [ F ] [ x

      word-r;  // [ K [ F ] [ x ]
      word-c;  // [ K [ F ] [ x ]
  
      word-r;  // [ K [ F ] [ x ] ]
      word-c;  // [ K [ F ] [ x ] ]
   
      word-l;  // [ K [ F ] [ x ] ] [
      word-c;  // [ K [ F ] [ x ] ] [

      term-k;  // [ K [ F ] [ x ] ] [ K
      word-t;  // [ K [ F ] [ x ] ] [ K
      word-c;  // [ K [ F ] [ x ] ] [ K
  
      word-l;  // [ K [ F ] [ x ] ] [ K [
      word-c;  // [ K [ F ] [ x ] ] [ K [

      term-t;  // [ K [ F ] [ x ] ] [ K [ T
      word-t;  // [ K [ F ] [ x ] ] [ K [ T
      word-c;  // [ K [ F ] [ x ] ] [ K [ T

      word-r;  // [ K [ F ] [ x ] ] [ K [ T ]
      word-c;  // [ K [ F ] [ x ] ] [ K [ T ]

      word-l;  // [ K [ F ] [ x ] ] [ K [ T ] [
      word-c;  // [ K [ F ] [ x ] ] [ K [ T ] [

      termx;   // [ K [ F ] [ x ] ] [ K [ T ] [ x
      word-t;  // [ K [ F ] [ x ] ] [ K [ T ] [ x
      word-c;  // [ K [ F ] [ x ] ] [ K [ T ] [ x

      word-r;  // [ K [ F ] [ x ] ] [ K [ T ] [ x ]
      word-c;  // [ K [ F ] [ x ] ] [ K [ T ] [ x ]

      word-r;  // [ K [ F ] [ x ] ] [ K [ T ] [ x ] ]
      word-c;  // [ K [ F ] [ x ] ] [ K [ T ] [ x ] ]

      not.t;
      word-c; // tail'''' = [ K [ F ] [ x ] ] [ K [ T ] [ x ] ] tail

        not.h;

        term-i; // x''' = I

        term-k;
        term-f;
        term-c; // y''' = K [ F ]

        termx; // z''' = x

        // constructing the tail [ K [ T ] [ x ] ] 

        word-l;  // [

        term-k;  // [ K
        word-t;  // [ K
        word-c;  // [ K

        word-l;  // [ K [
        word-c;  // [ K [

        term-t;  // [ K [ T
        word-t;  // [ K [ T
        word-c;  // [ K [ T

        word-r;  // [ K [ T ]
        word-c;  // [ K [ T ]

        word-l;  // [ K [ T ] [
        word-c;  // [ K [ T ] [

        termx;  // [ K [ T ] [ x
        word-t; // [ K [ T ] [ x
        word-c; // [ K [ T ] [ x

        word-r;  // [ K [ T ] [ x ]
        word-c;  // [ K [ T ] [ x ]

        word-r;  // [ K [ T ] [ x ] ]
        word-c;  // [ K [ T ] [ x ] ]

        not.t; // tail
        word-c;  // tail' = [ K [ T ] [ x ] ] tail

          not.h;

          // S [ I ] [ K [ F ] ]
          term-s; // S
          term-i; // I
          term-c; // S [ I ]

          term-k; // K
          term-f; // F
          term-c; // K [ F ]

          term-c; // x'' = S [ I ] [ K [ F ] ]

          //  K [ T ]
          term-k; // K
          term-t; // T
          term-c; // y'' = K [ T ]

          // x
          termx; // z'' = x

          not.t;

            not.h; // head'

            term-not; // x' = NOT

            term-s; // S

            term-s;
            term-i;
            term-c; // S [ I ]

            term-k; 
            term-f;
            term-c; // K [ F ]

            term-c; // S [ I ] [ K [ F ] ]

            term-c; // S [ S [ I ] [ K [ F ] ] ]

            term-k;
            term-t;
            term-c; // K [ T ]

            term-c; // y' = S [ S [ I ] [ K [ F ] ] ] [ K [ T ] ]

            // constructing the tail
            word-l;  // [

            termx;   // [ x
            word-t;  // [ x
            word-c;  // [ x

            word-r;  // [ x ]
            word-c;  // [ x ]

            not.t; // tail
            word-c;  // tail' = [ x ] tail

            df-not; // NOT = S [ S [ I ] [ K [ F ] ] ] [ K [ T ] ]

            not-e;  // head NOT [ x ] tail

            // |- head S [ S [ I ] [ K [ F ] ] ] [ K [ T ] ] [ x ] tail
            df-eq;  // head' y' tail' = head S [ K ] [ x' ] [ y' ] tail

          ax-s; // head S [ I ] [ K [ F ] ] [ x ] [ K [ T ] [ x ] ] tail

        ax-s; // head I [ x ] [ K [ F ] [ x ] ] [ K [ T ] [ x ] ] tail

      id;

    ax-k;

  ax-k;
  };

  return |- head x [ F ] [ T ] tail;
}

axiom term-or() {
  return term OR;
}

axiom df-or() {
  return |- OR = S [ I ] [ K [ T ] ];
}

theorem or(
  or.h: word head,
  term-x: term x,
  term-y: term y,
  or.t: word tail) {

  assume or-e: |- head OR [ x ] [ y ] tail;

  do {

  // head x [ K [ T ] [ x ] ] [ y ] tail

  or.h;   // head
  term-x; // head x
  word-t; // head x
  word-c; // head x

  word-l; // head x [
  word-c; // head x [

  term-t; // x'''' = T
  term-x; // y'''' = x

  word-r; // ]
  word-l; // ] [
  word-c; // ] [

  term-y; // ] [ y
  word-t; // ] [ y
  word-c; // ] [ y

  word-r; // ] [ y ]
  word-c; // ] [ y ]

  or.t;   // tail''''
  word-c; //  ] [ y ] tail''''

    // head I [ x ] [ K [ T ] [ x ] ] [ y ] tail
    or.h; // head'''

    term-x; // x''' = x

    // constructing tail'''
    word-l;  // [

    term-k;  // [ K
    word-t;  // [ K
    word-c;  // [ K

    word-l;  // [ K [
    word-c;  // [ K [

    term-t;  // [ K [ T
    word-t;  // [ K [ T
    word-c;  // [ K [ T

    word-r;  // [ K [ T ]
    word-c;  // [ K [ T ]
    
    word-l;  // [ K [ T ] [
    word-c;  // [ K [ T ] [
    
    term-x;  // [ K [ T ] [ x
    word-t;  // [ K [ T ] [ x
    word-c;  // [ K [ T ] [ x

    word-r;  // [ K [ T ] [ x ]
    word-c;  // [ K [ T ] [ x ]
    
    word-r;  // [ K [ T ] [ x ] ]
    word-c;  // [ K [ T ] [ x ] ]
    
    word-l;  // [ K [ T ] [ x ] ] [
    word-c;  // [ K [ T ] [ x ] ] [
    
    term-y;  // [ K [ T ] [ x ] ] [ y
    word-t;  // [ K [ T ] [ x ] ] [ y
    word-c;  // [ K [ T ] [ x ] ] [ y

    word-r;  // [ K [ T ] [ x ] ] [ y ]
    word-c;  // [ K [ T ] [ x ] ] [ y ]

    or.t;    // tail
    word-c;  // tail'' = [ K ] tail

      // head S [ I ] [ K [ T ] ] [ x ] [ y ] tail

      or.h;  // head

      term-i;  // x'' = I

      term-k;  // K
      term-t;  // T
      term-c;  // y'' = K [ T ]

      term-x;  // z'' = x

      word-l;  // [

      term-y;  // [ y
      word-t;  // [ y
      word-c;  // [ y

      word-r;  // [ y ]
      word-c;  // [ y ]
    
      or.t;    // tail
      word-c;  // tail'' = [ y ] tail

        or.h; // head'

        term-or;  // x' = OR

        term-s;  // S
        term-i;  // I
        term-c;  // S [ I ]

        term-k;  // K
        term-t;  // T
        term-c;  // K [ T ]

        term-c;  // y' = S [ I ] [ K [ T ] ]

        word-l;  // [

        termx;   // [ x
        word-t;  // [ x
        word-c;  // [ x

        word-r;  // [ x ]
        word-c;  // [ x ]

        word-l;  // [ x ] [
        word-c;  // [ x ] [

        termy;   // [ x ] [ y
        word-t;  // [ x ] [ y
        word-c;  // [ x ] [ y

        word-r;  // [ x ] [ y ]
        word-c;  // [ x ] [ y ]

        or.t; // tail
        word-c;  // tail' = [ x ] [ y ] tail

        df-or; // OR = S [ K ]

        or-e;  // head OR [ x ] [ y ] tail

        df-eq;  // head' y' tail' = head S [ I ] [ K [ T ] ] [ x ] [ y ] tail

      ax-s; // head I [ x ] [ K [ T ] [ x ] ] [ y ] tail

    id; // head x [ K [ T ] [ x ] ] [ y ] tail

    ax-k; // head x [ T ] [ y ] tail
  };

  return |- head x [ T ] [ y ] tail;
}

axiom term-and() {
  return term AND;
}


axiom df-and() {
  return |- AND = S [ S ] [ K [ K [ F ] ] ];
}

theorem and(
  and.h: word head,
  term-x: term x,
  term-y: term y,
  and.t: word tail) {

  assume and-e: |- head AND [ x ] [ y ] tail;

  do {

  // head x [ y ] [ K [ F ] [ y ] ] tail

  and.h; // head

  term-x; // x
  word-t; // x
  word-c; // head x

  word-l; // head x [
  word-c; // head x [

  term-y; // y
  word-t; // y
  word-c; // head x [ y

  word-r; // head x [ y ]
  word-c; // head x [ y ]
  
  word-l; // head x [ y ] [
  word-c; // head''''' = head x [ y ] [

  term-f; // x''''' = F

  term-y; // y''''' = y

  word-r;  // ]
  and.t;   // tail
  word-c;  // tail''''' = ] tail

    // head x [ y ] [ K [ K [ F ] ] [ x ] [ y ] ] tail

    and.h; // head

    term-x; // x
    word-t; // x
    word-c; // head x

    word-l; // head x [
    word-c; // head x [

    term-y; // y
    word-t; // y
    word-c; // head x [ y

    word-r; // head x [ y ]
    word-c; // head x [ y ]
  
    word-l; // head x [ y ] [
    word-c; // head'''' = head x [ y ] [

    term-k; // K
    term-f; // F
    term-c; // x'''' = K [ F ]

    term-x; // y'''' = x

    word-l;  // [

    term-y;  // [ y
    word-t;  // [ y
    word-c;  // [ y

    word-r;  // [ y ]
    word-c;  // [ y ]

    word-r;  // [ y ] ]
    word-c;  // [ y ] ]

    and.t;   // tail
    word-c;  // tail' = [ y ] ] tail
  
      // head S [ x ] [ K [ K [ F ] ] [ x ] ] [ y ] tail

      and.h; // head '''

      term-x; // x''' = x

      term-k;  // K
      term-k;  // K
      term-f;  // F
      term-c;  // K [ F ]
      term-c;  // K [ K [ F ] ]

      term-x;  // x
      term-c;  // y''' = K [ K [ F ] ] [ x ]

      term-y;  // z''' = y

      and.t;   // tail

        // head S [ S ] [ K [ K [ F ] ] ] [ x ] [ y ] tail

        and.h; // head''

        term-s; // x'' = S

        term-k;  // K
        term-k;  // K
        term-f;  // F
        term-c;  // K [ F ]
        term-c;  // y'' = K [ K [ F ] ]

        term-x;  // z'' = x
      
        word-l;  // [

        term-y;  // [ y
        word-t;  // [ y
        word-c;  // [ y

        word-r;  // [ y ]
        word-c;  // [ y ]

        and.t;   // tail
        word-c;  // tail' = [ y ] tail

          and.h; // head'

          term-and;  // x' = AND

          term-s;  // S
          term-s;  // S
          term-c;  // S [ S ]

          term-k;  // K
          term-k;  // K
          term-f;  // F
          term-c;  // K [ F ]
          term-c;  // K [ K [ f ] ]

          term-c;  // y' = S [ S ] [ K [ K [ F ] ] ]

          word-l;  // [

          termx;   // [ x
          word-t;  // [ x
          word-c;  // [ x

          word-r;  // [ x ]
          word-c;  // [ x ]

          word-l;  // [ x ] [
          word-c;  // [ x ] [

          termy;   // [ x ] [ y
          word-t;  // [ x ] [ y
          word-c;  // [ x ] [ y

          word-r;  // [ x ] [ y ]
          word-c;  // [ x ] [ y ]

          and.t; // tail
          word-c;  // tail' = [ x ] [ y ] tail

          df-and; // AND = S [ S ] [ K [ K [ F ] ] ]

          and-e;  // head AND [ x ] [ y ] tail

          df-eq;  // head' y' tail' = head S [ S ] [ K [ K [ F ] ] ] [ x ] [ y ] tail

        ax-s; // head S [ x ] [ K [ K [ F ] ] [ x ] ] [ y ] tail

      ax-s; // head x [ y ] [ K [ K [ F ] ] [ x ] [ y ] ] tail

    ax-k; // head x [ y ] [ K [ F ] [ y ] ] tail

  ax-k; // head x [ y ] [ F ] tail
  };

  return |- head x [ y ] [ F ] tail;
}

axiom term-nand() {
  return term NAND;
}


axiom df-nand(term x, term y) {
  return |- NAND [ x ] [ y ] = NOT [ AND [ x ] [ y ] ];
}

theorem nand(
  nand.h: word head,
  term-x: term x,
  term-y: term y,
  nand.t: word tail) {

  assume nand-e: |- head NAND [ x ] [ y ] tail;

  do {

  // head AND [ x ] [ y ] [ F ] [ T ] tail

  nand.h; // head

  term-x; // x'''' = x
  term-y; // y'''' = y

  word-l; // [
  term-f; // F
  word-t; // F
  word-c; // [ F

  word-r; // ]
  word-c; // [ F ]

  word-l; // [
  word-c; // [ F ] [

  term-t; // T
  word-t; // T
  word-c; // [ F ] [ T

  word-r; // ]
  word-c; // [ F ] [ T ]

  nand.t; // tail
  word-c; // [ F ] [ T ] tail

    // head NOT [ AND [ x ] [ y ] ] tail

    nand.h; // head

    term-and; // AND
    term-x;   // x
    term-c;   // AND [ x ]
    term-y;   // y
    term-c;   // x ''' = AND [ x ] [ y ]

    nand.t;  // tai

      nand.h; // head

      term-nand; // NAND
      term-x;    // x
      term-c;    // NAND [ x ]

      term-y;    // y
      term-c;    // x' = NAND [ x ] [ y ]

      term-not;  // NOT

      term-and;  // AND
      term-x;    // x
      term-c;    // AND [ x ]
      term-y;    // y
      term-c;    // AND [ x ] [ y ]

      term-c;    // y' = NOT [ AND [ x ] [ y ] ]

      nand.t; // tail

      term-x; // x = x

      term-y; // y = y

      df-nand; // |- NAND [ x ] [ y ] = NOT [ AND [ x ] [ y ] ]

      nand-e; // |- head NAND [ x ] [ y ] tail

      df-eq; // head NOT [ AND [ x ] [ y ] ] tail

    not; // head AND [ x ] [ y ] [ F ] [ T ] tail

  and; // head x [ y ] [ F ] [ F ] [ T ] tail    
  };

  return |- head x [ y ] [ F ] [ F ] [ T ] tail;
}

axiom term-h() {
  return term H;
}

axiom df-h(term x, term y) {
  return |- H [ x ] [ y ] = F [ x ] [ y ];
}

theorem h(
  h.h: word head,
  term-x: term x,
  term-y: term y,
  h.t: word tail) {

  assume h-e: |- head H [ x ] [ y ] tail;

  do {

  // head F [ x ] [ y ] tail

  h.h;

  term-x; // x'' = x

  term-y; // y'' = y

  h.t;

    h.h;

    term-h; // H
    term-x; // x
    term-c; // H [ x ] 
    term-y; // y
    term-c; // x' = H [ x ] [ y ]

    term-f; // F
    term-x; // x
    term-c; // F [ x ] 
    term-y; // y
    term-c; // y' = F [ x ] [ y ]

    h.t;

    term-x;
    term-y;
    df-h;

    h-e;
    df-eq; // head F [ x ] [ y ] tail

  false; // head y tail
  };

  return |- head y tail;
}

axiom term-b() {
  return term B;
}

axiom df-b(term f, term g, term x) {
  return |- B [ f ] [ g ] [ x ] = S [ K [ S ] ] [ K ] [ f ] [ g ] [ x ];
}

theorem b(
  b.h: word head,
  f: term f,
  g: term g,
  x: term x,
  b.t: word tail) {

  assume b-e: |- head B [ f ] [ g ] [ x ] tail;

  do {

  // head K [ f ] [ x ] [ g [ x ] ] tail

  b.h;

  f;

  x;

  word-l; // [
  g;      // g
  word-t; // g
  word-c; // [ g

  word-l; // [
  word-c; // [ g [

  x;      // x
  word-t; // x
  word-c; // [ g [ x

  word-r; // ]
  word-c; // [ g [ x ]

  word-r; // ]
  word-c; // [ g [ x ] ]

  b.t;    // tail
  word-c; // [ g [ x ] ] tail

    // head S [ K [ f ] ] [ g ] [ x ] tail

    b.h;

    term-k; // K
    f;      // f
    term-c; // K [ f ]

    g;      // g

    x;      // x

    b.t;

      // head K [ S ] [ f ] [ K [ f ] ] [ g ] [ x ] tail

      b.h;

      term-s; // x''' = S
      f;      // y''' = f

      word-l; // [
      term-k; // K
      word-t; // K
      word-c; // [ K

      word-l; // [
      word-c; // [ K [
 
      f;      // f
      word-t; // f
      word-c; // [ K [ f

      word-r; // ]
      word-c; // [ K [ f ]

      word-r; // ]
      word-c; // [ K [ f ] ]

      word-l; // [
      g;      // g
      word-t; // g
      word-c; // [ g

      word-r; // ]
      word-c; // [ g ]

      word-l; // [
      word-c; // [ g ] [

      x;      // x
      word-t; // x
      word-c; // [ g ] [ x

      word-r; // ]
      word-c; // [ g ] [ x ]

      word-c; // [ K [ f ] ] [ g ] [ x ]

      b.t;    // tail
      word-c; // tail'' = [ K [ f ] ] [ g ] [ x ] tail

        // head S [ K [ S ] ] [ K ] [ f ] [ g ] [ x ] tail

        b.h;

        term-k;
        term-s;
        term-c; // x'' = K [ S ]

        term-k; // y'' = K

        f;      // z'' = f

        word-l; // [
        g;      // g
        word-t; // g
        word-c; // [ g

        word-r; // ]
        word-c; // [ g ]

        word-l; // [
        word-c; // [ g ] [

        x;      // x
        word-t; // x
        word-c; // [ g ] [ x

        word-r; // ]
        word-c; // [ g ] [ x ]

        b.t;    // tail
        word-c; // tail'' = [ g ] [ x ] tail

          b.h;

          term-b; // B
          f;      // f
          term-c; // B [ f ] 
          g;      // g
          term-c; // B [ f ] [ g ]
          x;      // x
          term-c; // B [ f ] [ g ] [ x ]

          term-s; // S
          term-k; // K
          term-s; // S
          term-c; // K [ S ]
          term-c; // S [ K [ S ] ]
          term-k; // K
          term-c; // S [ K [ S ] ] [ K ]
          f;      // f
          term-c; // S [ K [ S ] ] [ K ] [ f ] 
          g;      // g
          term-c; // S [ K [ S ] ] [ K ] [ f ] [ g ]
          x;      // x
          term-c; // S [ K [ S ] ] [ K ] [ f ] [ g ] [ x ]

          b.t;

          f;
          g;
          x;
          df-b; // |- B [ f ] [ g ] [ x ] = S [ K [ S ] ] [ K ] [ f ] [ g ] [ x ]

          b-e; // |- head B [ f ] [ g ] [ x ] tail

          df-eq; // head S [ K [ S ] ] [ K ] [ f ] [ g ] [ x ] tail

        ax-s; // head K [ S ] [ f ] [ K [ f ] ] [ g ] [ x ] tail

      ax-k; // head S [ K [ f ] ] [ g ] [ x ] tail

    ax-s; // head K [ f ] [ x ] [ g [ x ] ] tail

  ax-k; // head f [ g [ x ] ] tail
  };

  return |- head f [ g [ x ] ] tail;
}

axiom term-C() {
  return term C;
}

axiom df-c(term f, term g, term x) {
  return |- C [ f ] [ g ] [ x ] = S [ B [ B ] [ S ] ] [ K [ K ] ] [ f ] [ g ] [ x ];
}

theorem c(
  head: word head,
  f: term f,
  g: term g,
  x: term x,
  tail: word tail) {

  assume c-e: |- head C [ f ] [ g ] [ x ] tail;

  do {

  // head f [ x ] [ K [ g ] [ x ] ] tail
  head;
  f;
  word-t;
  word-c; // head f
  word-l;
  word-c; // head f [
  x;
  word-t;
  word-c; // head f [ x
  word-r;
  word-c; // head f [ x ]
  word-l;
  word-c; // head f [ x ] [

  g;      // x = g
  x;      // y = x

  word-r;
  tail;
  word-c; // ] tail

    // head f [ x ] [ K [ K ] [ f ] [ g ] [ x ] ] tail

    head;
    f;
    word-t;
    word-c; // head f
    word-l;
    word-c; // head f [
    x;
    word-t;
    word-c; // head f [ x
    word-r;
    word-c; // head f [ x ]
    word-l;
    word-c; // head f [ x ] [

    term-k; // x = K
    f;      // y = f

    word-l;  // [

    g;       // g
    word-t;  // g
    word-c;  // [ g

    word-r;  // ]
    word-c;  // [ g ]

    word-l;  // [
    word-c;  // [ g ] [

    x;       // x
    word-t;  // x
    word-c;  // [ g ] [ x

    word-r;  // ]
    word-c;  // [ g ] [ x ]

    word-r;  // ]
    word-c;  // [ g ] [ x ] ]
    
    tail;    // tail
    word-c;  // [ g ] [ x ] ] tail

      // head S [ f ] [ K [ K ] [ f ] [ g ] ] [ x ] tail

      head;

      f;      // x = f

      term-k;
      term-k;
      term-c; // K [ K ]
      f;
      term-c; // K [ K ] [ f ]
      g;
      term-c; // y = K [ K ] [ f ] [ g ]

      x;

      tail;


        // head B [ S [ f ] ] [ K [ K ] [ f ] ] [ g ] [ x ] tail

        head;

        term-s;
        f;
        term-c;  // f = S [ f ]

        term-k;
        term-k;
        term-c;  // K [ K ]
        f;
        term-c;  // g = K [ K ] [ f ]

        g;       // x = g

        word-l;  // [
        x;       // x
        word-t;  // x
        word-c;  // [ x

        word-r;  // ]
        word-c;  // [ x ]

        tail;    // tail
        word-c;  // [ x ] tail

          // head B [ B ] [ S ] [ f ] [ K [ K ] [ f ] ] [ g ] [ x ] tail

          head;
 
          term-b;
          term-s;
          f;

          word-l; // [
          term-k; // K
          word-t; // K
          word-c; // [ K

          word-l; // [
          word-c; // [ K [

          term-k; // K
          word-t; // K
          word-c; // [ K [ K

          word-r; // ]
          word-c; // [ K [ K ]

          word-l; // [
          word-c; // [ K [ K ] [

          f;      // f
          word-t; // f
          word-c; // [ K [ K ] [ f

          word-r; // ]
          word-c; // [ K [ K ] [ f ]

          word-r; // ]
          word-c; // [ K [ K ] [ f ] ]

          word-l;  // [
          word-c;  // [ K [ K ] [ f ] ] [

          g;       // g
          word-t;  // g
          word-c;  // [ K [ K ] [ f ] ] [ g

          word-r;  // ]
          word-c;  // [ K [ K ] [ f ] ] [ g ]

          word-l;  // [
          word-c;  // [ K [ K ] [ f ] ] [ g ] [

          x;       // x
          word-t;  // x
          word-c;  // [ K [ K ] [ f ] ] [ g ] [ x

          word-r;  // ]
          word-c;  // [ K [ K ] [ f ] ] [ g ] [ x ]

          tail;    // tail
          word-c;  // [ K [ K ] [ f ] ] [ g ] [ x ] tail

            // head S [ B [ B ] [ S ] ] [ K [ K ] ] [ f ] [ g ] [ x ] tail

            head;

            term-b;  // B
            term-b;  // B
            term-c;  // B [ B ]
            term-s;  // S
            term-c;  // B [ B ] [ S ]

            term-k;  // K
            term-k;  // K
            term-c;  // K [ K ]

            f;

            word-l;  // [

            g;       // g
            word-t;  // g
            word-c;  // [ g

            word-r;  // ]
            word-c;  // [ g ]

            word-l;  // [
            word-c;  // [ g ] [

            x;       // x
            word-t;  // x
            word-c;  // [ g ] [ x

            word-r;  // ]
            word-c;  // [ g ] [ x ]

            tail;    // tail
            word-c;  // [ g ] [ x ] tail

              head;

              term-C; // C
              f;      // f
              term-c; // C [ f ] 
              g;      // g
              term-c; // C [ f ] [ g ]
              x;      // x
              term-c; // C [ f ] [ g ] [ x ]

              term-s; // S
              term-b; // B
              term-b; // B
              term-c; // B [ B ]
              term-s; // S
              term-c; // B [ B ] [ S ]
              term-c; // S [ B [ B ] [ S ] ]
              term-k; // K
              term-k; // K
              term-c; // K [ K ]
              term-c; // S [ B [ B ] [ S ] ] [ K [ K ] ]
              f;      // f
              term-c; // S [ B [ B ] [ S ] ] [ K [ K ] ] [ f ] 
              g;      // g
              term-c; // S [ B [ B ] [ S ] ] [ K [ K ] ] [ f ] [ g ]
              x;      // x
              term-c; // S [ B [ B ] [ S ] ] [ K [ K ] ] [ f ] [ g ] [ x ]

              tail;

              f;
              g;
              x;
              df-c; // |- C [ f ] [ g ] [ x ] = S [ B [ B ] [ S ] ] [ K [ K ] ] [ f ] [ g ] [ x ]

              c-e; // |- head C [ f ] [ g ] [ x ] tail

              df-eq; // head S [ B [ B ] [ S ] ] [ K [ K ] ] [ f ] [ g ] [ x ] tail

            ax-s; // head B [ B ] [ S ] [ f ] [ K [ K ] [ f ] ] [ g ] [ x ] tail

          b; // head B [ S [ f ] ] [ K [ K ] [ f ] ] [ g ] [ x ] tail

        b; // head S [ f ] [ K [ K ] [ f ] [ g ] ] [ x ] tail

      ax-s; // head f [ x ] [ K [ K ] [ f ] [ g ] [ x ] ] tail

    ax-k; // head f [ x ] [ K [ g ] [ x ] ] tail

  ax-k; 
  };

  return |- head f [ x ] [ g ] tail;
}

axiom term-W() {
  return term W;
}

axiom df-w(term x, term f) {
  return |- W [ x ] [ f ] = C [ I ] [ x ] [ f ];
}

theorem w(
  head: word head,
  x: term x,
  f: term f,
  tail: word tail) {

  assume w-e: |- head W [ x ] [ f ] tail;

  do {

    // "head I [ f ] [ x ] tail

    head;

    f; // x = f

    word-l;

    x;
    word-t;
    word-c; // [ x

    word-r;
    word-c; // [ x ]

    tail;
    word-c; // [ x ] tail

      // head C [ I ] [ x ] [ f ] tail
      head;

      term-i;
      x;
      f;

      tail;
    

              head;

              term-W; // W
              x;      // x
              term-c; // W [ x ] 
              f;      // f
              term-c; // W [ x ] [ f ]

              term-C;
              term-i;
              term-c; // C [ I ]
              x;
              term-c; // C [ I ] [ x ]
              f;
              term-c; // C [ I ] [ x ] [ f ]

              tail;

              x;
              f;
              df-w; // |- W [ x ] [ f ] = C [ I ] [ x ] [ f ]

              w-e; // |- head W [ x ] [ f ] tail

              df-eq; // head tail

       c;

    id;

  };
  return |- head f [ x ] tail;
}


axiom term-v() {
  return term V;
}

axiom df-v(term x, term y, term z) {
  return |- V [ x ] [ y ] [ z ] = B [ C ] [ W ] [ x ] [ y ] [ z ];
}

theorem v(
  head: word head,
  x: term x,
  y: term y,
  z: term z,
  tail: word tail) {

  assume v-e: |- head V [ x ] [ y ] [ z ] tail;

  do {

  // head W [ x ] [ z ] [ y ] tail

  head;

  x;
  z;

  word-l;
  y;
  word-t;
  word-c; // [ y
  word-r;
  word-c; // [ y ]
  tail;
  word-c; // [ y ] tail

    // head C [ W [ x ] ] [ y ] [ z ] tail

    head;

    term-W;
    x;
    term-c; // f = W [ x ]

    y;      // g = y

    z;      // x = z

    tail;

      // head B [ C ] [ W ] [ x ] [ y ] [ z ] tail
      head;

      term-C; // f = C
      term-W; // g = W
      x;      // x = x

      word-l;
      y;
      word-t;
      word-c; // [ y
      word-r;
      word-c; // [ y ]
      word-l;
      word-c; // [ y ] [
      z;
      word-t;
      word-c; // [ y ] [ z
      word-r;
      word-c; // [ y ] [ z ]
      tail;
      word-c; // [ y ] [ z ] tail

              head;

              term-v; // V
              x;      // x
              term-c; // V [ x ] 
              y;      // y
              term-c; // V [ x ] [ y ]
              z;      // z
              term-c; // V [ x ] [ y ] [ z ]

              term-b; // B
              term-C; // C
              term-c; // B [ C ]
              term-W; // W
              term-c; // B [ C ] [ W ]
              x;      // x
              term-c; // B [ C ] [ W ] [ x ] 
              y;      // y
              term-c; // B [ C ] [ W ] [ x ] [ y ]
              z;      // z
              term-c; // B [ C ] [ W ] [ x ] [ y ] [ z ]

              tail;

              x;
              y;
              z;
              df-v; // |- V [ x ] [ y ] [ z ] = B [ C ] [ W ] [ x ] [ y ] [ z ]

              v-e; // |- head V [ x ] [ y ] [ z ] tail

              df-eq; // head B [ C ] [ W ] [ x ] [ y ] [ z ] tail

        b; // head C [ W [ x ] ] [ y ] [ z ] tail

    c; // head W [ x ] [ z ] [ y ] tail

  w;

  };

  return |- head z [ x ] [ y ] tail;
}

axiom term-pair() {
  return term Pair;
}

axiom df-pair(term x, term y, term z) {
  return |- Pair [ x ] [ y ] [ z ] = V [ x ] [ y ] [ z ];
}

theorem pair(
  head: word head,
  x: term x,
  y: term y,
  z: term z,
  tail: word tail) {

  assume pair-e: |- head Pair [ x ] [ y ] [ z ] tail;

  do {

    // head V [ x ] [ y ] [ z ] tail

    head;
    x;
    y;
    z;
    tail;
    
              head;

              term-pair; // Pair
              x;      // x
              term-c; // Pair [ x ] 
              y;      // y
              term-c; // Pair [ x ] [ y ]
              z;      // z
              term-c; // Pair [ x ] [ y ] [ z ]

              term-v; // V
              x;      // x
              term-c; // V [ x ] 
              y;      // y
              term-c; // V [ x ] [ y ]
              z;      // z
              term-c; // V [ x ] [ y ] [ z ]

              tail;

              x;
              y;
              z;
              df-pair; // |- Pair [ x ] [ y ] [ z ] = V [ x ] [ y ] [ z ] 

              pair-e; // |- head Pair [ x ] [ y ] [ z ] tail

              df-eq; // head V [ x ] [ y ] [ z ] tail
    v;

  };

  return |- head z [ x ] [ y ] tail;
}

axiom term-first() {
  return term First;
}

axiom df-first() {
  return |- First = W [ T ];
}

theorem first(
  head: word head,
  x: term x,
  y: term y,
  tail: word tail) {

  assume first-e: |- head First [ Pair [ x ] [ y ] ] tail;

  do {

  // head T [ x ] [ y ] tail

  head;

  x;
  y;

  tail;

    // head Pair [ x ] [ y ] [ T ] tail

    head;

    x;
    y;
    term-t;

    tail;

      // head W [ T ] [ Pair [ x ] [ y ] ] tail

      head;

      term-t;
      term-pair;
      x;
      term-c;
      y;
      term-c;

      tail;

              head;

              term-first;

              term-W;
              term-t;
              term-c;

              word-l;
              term-pair;
              word-t;
              word-c; // [ Pair
              word-l;
              word-c; // [ Pair [
              x;
              word-t;
              word-c; // [ Pair [ x
              word-r;
              word-c; // [ Pair [ x ]
              word-l; // 
              word-c; // [ Pair [ x ] [
              y;
              word-t;
              word-c; // [ Pair [ x ] [ y
              word-r;
              word-c; // [ Pair [ x ] [ y ]
              word-r;
              word-c; // [ Pair [ x ] [ y ] ]

              tail;
              word-c; // [ Pair [ x ] [ y ] ] tail

              df-first; // |- First = W [ T ]

              first-e; // |- head First [ Pair [ x ] [ y ] ] tail

              df-eq; // head W [ T ] [ Pair [ x ] [ y ] ] tail

      w; // head Pair [ x ] [ y ] [ T ] tail

    pair; // head T [ x ] [ y ] tail

  true;
  };

  return |- head x tail;
}

axiom term-second() {
  return term Second;
}

axiom df-second() {
  return |- Second = W [ F ];
}

theorem second(
  head: word head,
  x: term x,
  y: term y,
  tail: word tail) {

  assume second-e: |- head Second [ Pair [ x ] [ y ] ] tail;

  do {

  // head F [ x ] [ y ] tail

  head;

  x;
  y;

  tail;

    // head Pair [ x ] [ y ] [ F ] tail

    head;

    x;
    y;
    term-f;

    tail;

      // head W [ T ] [ Pair [ x ] [ y ] ] tail

      head;

      term-f;
      term-pair;
      x;
      term-c;
      y;
      term-c;

      tail;

              head;

              term-second;

              term-W;
              term-f;
              term-c; // W [ F ]

              word-l;
              term-pair;
              word-t;
              word-c; // [ Pair
              word-l;
              word-c; // [ Pair [
              x;
              word-t;
              word-c; // [ Pair [ x
              word-r;
              word-c; // [ Pair [ x ]
              word-l; // 
              word-c; // [ Pair [ x ] [
              y;
              word-t;
              word-c; // [ Pair [ x ] [ y
              word-r;
              word-c; // [ Pair [ x ] [ y ]
              word-r;
              word-c; // [ Pair [ x ] [ y ] ]

              tail;
              word-c; // [ Pair [ x ] [ y ] ] tail

              df-second; // |- Second = W [ F ]

              second-e; // |- head Second [ Pair [ x ] [ y ] ] tail

              df-eq; // head W [ F ] [ Pair [ x ] [ y ] ] tail

      w; // head Pair [ x ] [ y ] [ F ] tail

    pair; // head F [ x ] [ y ] tail

  false;
  };

  return |- head y tail;
}

axiom term-0() {
  return term 0;
}

axiom df-0() {
  return |- 0 = I;
}

axiom term-Zero() {
  return term Zero;
}

axiom df-Zero(term x) {
  return |- Zero [ x ]  = First [ x ];
}

//theorem z0eT() {
//  do {
    

//    term-0;
//    df-Zero; // Zero [ 0 ] = First [ 0 ]
//  };

//  return |- Zero [ 0 ] = T;
//}

theorem Zero0(
  head: word head,
  tail: word tail) {

  assume zero-e: |- head Zero [ 0 ] tail;

  do {

    // head I [ T ] tail

    head;
    term-t;
    tail;

      // head 0 [ T ] tail

      head;

      term-0;

      term-i;

      word-l;
      term-t;
      word-t;
      word-c; // [ T
      word-r;
      word-c; // [ T ]
      tail;
      word-c; // [ T ] tail

      df-0;

        // head W [ T ] [ 0 ] tail

        head;

        term-t;
        term-0;

        tail;


          // head First [ 0 ] tail

          head;

          term-first; // First

          term-W;
          term-t;
          term-c; // W [ T ]    

          word-l;
          term-0;
          word-t;
          word-c; // [ 0
          word-r;
          word-c; // [ 0 ]
          tail;
          word-c; // [ 0 ] tail

          df-first; // First = W [ T ]

              head;

              term-Zero;
              term-0;
              term-c; // Zero [ 0 ]

              term-first;
              term-0;
              term-c; // First [ 0 ]

              tail;

              term-0;

              df-Zero; // |- Zero [ 0 ] = First [ 0 ]

              zero-e; // |- Zero [ 0 ]

              df-eq; // |- head First [ 0 ] tail

           df-eq; // head W [ T ] [ 0 ] tail

         w; //

       df-eq; // head I [ T ] tail

    id;

  };

  return |- head T tail;
}

axiom term-1() {
  return term 1;
}

axiom df-1() {
  return |- 1 = Pair [ F ] [ 0 ];
}

axiom term-Next() {
  return term Next;
}

axiom df-Next(term x) {
  return |- Next [ x ] = Pair [ F ] [ x ];
}

axiom word-eq() {
  return word =;
}

theorem n0eq1() {

  do {

    // Next [ 0 ] = Pair [ F ] [ 0 ]

    term-Next;
    word-t;
    word-l;
    word-c; // Next [
    term-0;
    word-t;
    word-c; // Next [ 0
    word-r;
    word-c; // Next [ 0 ]
    word-eq;
    word-c; // Next [ 0 ] =

    term-pair;
    term-f;
    term-c; // Pair [ F ]
    term-0;
    term-c; // Pair [ F ] [ 0 ]

    term-1; // x = 1

    word-null;

      word-null;

      term-1; // 1

      term-pair;
      term-f;
      term-c;
      term-0;
      term-c; // Pair [ F ] [ 0 ]

      word-null;

      df-1; // 1 = Pair [ F ] [ 0 ]

      df-sym;

    term-0;
    df-Next; // Next [ 0 ] = Pair [ F ] [ 0 ]

    df-eq;

  };

  return |- Next [ 0 ] = 1;
}

axiom term-2() {
  return term 2;
}

axiom df-2() {
  return |- 2 = Pair [ F ] [ 1 ];
}

theorem n1e2() {

  do {

    // Next [ 1 ] = Pair [ F ] [ 1 ]

    term-Next;
    word-t;
    word-l;
    word-c; // Next [
    term-1;
    word-t;
    word-c; // Next [ 1
    word-r;
    word-c; // Next [ 1 ]
    word-eq;
    word-c; // Next [ 1 ] =

    term-pair;
    term-f;
    term-c; // Pair [ F ]
    term-1;
    term-c; // Pair [ F ] [ 1 ]

    term-2; // x = 2

    word-null;

      word-null;

      term-2; // 2

      term-pair;
      term-f;
      term-c;
      term-1;
      term-c; // Pair [ F ] [ 1 ]

      word-null;

      df-2; // 2 = Pair [ F ] [ 1 ]

      df-sym;

    term-1;
    df-Next; // Next [ 1 ] = Pair [ F ] [ 1 ]

    df-eq;

  };

  return |- Next [ 1 ] = 2;
}

axiom term-Previous() {
  return term Previous;
}

axiom df-Previous(term x) {
  return |- Previous [ x ] = Second [ x ];
}

theorem p2e1() {

  do {

  // Previous [ 2 ] = Second [ Pair [ F ] [ 1 ] ]

  term-Previous;
  word-t;
  word-l;
  word-c;  // Previous [
  term-2;
  word-t;
  word-c;  // Previous [ 2
  word-r;
  word-c;  // Previous [ 2 ]
  word-eq;
  word-c;  // Previous [ 2 ]

  term-f;  // x = F
  term-1;  // y = 1

  word-null;


    // Previous [ 2 ] = Second [ 2 ]

    term-Previous;
    word-t;
    word-l;
    word-c;  // Previous [
    term-2;
    word-t;
    word-c;  // Previous [ 2
    word-r;
    word-c;  // Previous [ 2 ]
    word-eq;
    word-c;  // Previous [ 2 ] =
    term-second;
    word-t;
    word-c;  // Previous [ 2 ] = Second
    word-l;
    word-c;  // head = Previous [ 2 ] = Second [

    term-2;

    term-pair;
    term-f;
    term-c;  // Pair [ F ]
    term-1;
    term-c;  // Pair [ F ] [ 1 ]

    word-r;  // tail = ]

    df-2;

      term-2;
      df-Previous; // Previous [ 2 ] = Second [ 2 ]

    df-eq;

  second;

  };

  return |- Previous [ 2 ] = 1;
}

theorem p1e0() {

  do {

  // Previous [ 1 ] = Second [ Pair [ F ] [ 0 ] ]

  term-Previous;
  word-t;
  word-l;
  word-c;  // Previous [
  term-1;
  word-t;
  word-c;  // Previous [ 1
  word-r;
  word-c;  // Previous [ 1 ]
  word-eq;
  word-c;  // Previous [ 1 ]

  term-f;  // x = F
  term-0;  // y = 0

  word-null;

    // Previous [ 1 ] = Second [ 1 ]

    term-Previous;
    word-t;
    word-l;
    word-c;  // Previous [
    term-1;
    word-t;
    word-c;  // Previous [ 1
    word-r;
    word-c;  // Previous [ 1 ]
    word-eq;
    word-c;  // Previous [ 1 ] =
    term-second;
    word-t;
    word-c;  // Previous [ 1 ] = Second
    word-l;
    word-c;  // head = Previous [ 1 ] = Second [

    term-1;

    term-pair;
    term-f;
    term-c;  // Pair [ F ]
    term-0;
    term-c;  // Pair [ F ] [ 0 ]

    word-r;  // tail = ]

    df-1;

      term-1;
      df-Previous; // Previous [ 1 ] = Second [ 1 ]

    df-eq;

  second;

  };

  return |- Previous [ 1 ] = 0;
}

axiom term-Apply() {
  return term Apply;
}

// Apply[0, f, x] = x, Apply[1, f, x] = f(x), Apply[2, f, x] = f(f(x)), etc
axiom df-Apply(term n, term f, term x) {
  // Apply(n, f, x) {
  //   if n == 0
  //     return x
  //   else
  //    return f(Apply(n - 1, f, x))
  // }
  //                                  if n == 0 is T we get the first parameter, if F, the second
  return |- Apply [ n ] [ f ] [ x ] = Zero [ n ] [ x ] [ f [ Apply [ Previous [ n ] ] [ f ] [ x ] ] ];
}

theorem Apply0(
  head: word head,
  f: term f,
  x: term x,  
  tail: word tail) {

  assume apply0-e: |- head Apply [ 0 ] [ f ] [ x ] tail;

  do {

  // head T [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ] [ x ] ] ] tail

  head;

  x;

  f;
  term-Apply;
  term-Previous;
  term-0;
  term-c; // Previous [ 0 ]
  term-c; // Apply [ Previous [ 0 ] ]
  f;
  term-c; // Apply [ Previous [ 0 ] ] [ f ]
  x;
  term-c; // Apply [ Previous [ 0 ] ] [ f ] [ x ]
  term-c; // f [ Apply [ Previous [ 0 ] ] [ f ] [ x ] ]

  tail;  

    // head Zero [ 0 ] [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ] [ x ] ] ] tail

    head;

    word-l;
    x;
    word-t;
    word-c; // [ x  
    word-r;
    word-c; // [ x ]
    word-l;
    word-c; // [ x ] [
    f;
    word-t;
    word-c; // [ x ] [ f
    word-l;
    word-c; // [ x ] [ f [
    term-Apply;
    word-t;
    word-c; // [ x ] [ f [ Apply
    word-l;
    word-c; // [ x ] [ f [ Apply [
    term-Previous;
    word-t;
    word-c; // [ x ] [ f [ Apply [ Previous
    word-l;
    word-c; // [ x ] [ f [ Apply [ Previous [
    term-0;
    word-t;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0
    word-r;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0 ]
    word-r;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0 ] ]
    word-l;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0 ] ] [
    f;
    word-t;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f
    word-r;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ]
    word-l;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ] [
    x;
    word-t;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ] [ x
    word-r;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ] [ x ]
    word-r;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ] [ x ] ]
    word-r;
    word-c; // [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ] [ x ] ] ]
    tail;
    word-c; // tail = [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ] [ x ] ] ] tail

      // Apply [ 0 ] [ f ] [ x ] = Zero [ 0 ] [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ] [ x ] ] ]

      head;

      term-Apply;
      term-0;
      term-c; // Apply [ 0 ]
      f;
      term-c; // Apply [ 0 ] [ f ]
      x;
      term-c; // x = Apply [ 0 ] [ f ] [ 0 ]

      term-Zero;
      term-0;
      term-c; // Zero [ 0 ]
      x;
      term-c; // Zero [ 0 ] [ x ]
      f;
      term-Apply;
      term-Previous;
      term-0;
      term-c; // Previous [ 0 ]
      term-c; // Apply [ Previous [ 0 ] ]
      f;
      term-c; // Apply [ Previous [ 0 ] ] [ f ]
      x;
      term-c; // Apply [ Previous [ 0 ] ] [ f ]
      term-c; // f [ Apply [ Previous [ 0 ] ] [ f ] ]
      term-c; // y = Zero [ 0 ] [ x ] [ f [ Apply [ Previous [ 0 ] ] [ f ] ] ]

      tail;

        term-0;     // n = 0
        f;          // f = f
        x;          // x = x
        df-Apply;   // Apply [ 0 ] [ f ] [ x ]

      apply0-e; // |- head Apply [ 0 ] [ f ] [ x ] tail

      df-eq;

    Zero0;

  true;

  };

  return |- head x tail;
}

theorem Apply1(
  head: word head,
  f: term f,
  x: term x,  
  tail: word tail) {

  assume apply1-e: |- head Apply [ 1 ] [ f ] [ x ] tail;

  do {

  // head f [ Apply [ 0 ] [ f ] [ x ] ] tail

  head;
  f;
  word-t;
  word-c; // head f
  word-l;
  word-c; // head f [

  f;
  x;

  word-r;
  tail;
  word-c; // ] tail

    // head f [ Apply [ Previous [ 1 ] ] [ f ] [ x ] ] tail

    head;
    f;
    word-t;
    word-c; // head f
    word-l;
    word-c; // head f [
    term-Apply;
    word-t;
    word-c; // head f [ Apply
    word-l;
    word-c; // head f [ Apply [

    term-Previous;
    term-1;
    term-c; // x = Previous [ 1 ]

    term-0; // y = 0

    word-r;
    word-l;
    word-c; // ] [
    f;
    word-t;
    word-c; // ] [ f
    word-r;
    word-c; // ] [ f ]
    word-l;
    word-c; // ] [ f ] [
    x;
    word-t;
    word-c; // ] [ f ] [ x
    word-r;
    word-c; // ] [ f ] [ x ]
    word-r;
    word-c; // ] [ f ] [ x ] ]
    tail;
    word-c; // ] [ f ] [ x ] ] tail

    p1e0; // |- Previous [ 1 ] = 0


      // head F [ x ] [ f [ Apply [ Previous [ 1 ] ] [ f ] [ x ] ] ] tail

      head;

      x;

      f;
      term-Apply;
      term-Previous;
      term-1;
      term-c; // Previous [ 1 ]
      term-c; // Apply [ Previous [ 1 ] ]
      f;
      term-c; // Apply [ Previous [ 1 ] ] [ f ]
      x;
      term-c; // Apply [ Previous [ 1 ] ] [ f ] [ x ]
      term-c; // f [ Apply [ Previous [ 1 ] ] [ f ] [ x ] ]
  
      #; // save #1

      tail;

        // head Zero [ 1 ] [ x ] [ f [ Apply [ Previous [ 1 ] ] [ f ] [ x ] ] ] tail

        head;

        term-Zero;
        term-1;
        term-c; // x = Zero [ 1 ]

        term-f; // y = F

        word-l;
        x;
        word-t;
        word-c; // [ x
        word-r;
        word-c; // [ x ]
        word-l;
        word-c; // [ x ] [

        @0;

        word-t;
        word-c; // [ x ] [ f [ Apply [ Previous [ 1 ] ] [ f ] [ x ] ] ]

        word-r;
        word-c; // [ x ] [ f [ Apply [ Previous [ 1 ] ] [ f ] [ x ] ] ] ]
        tail;
        word-c; // [ x ] [ f [ Apply [ Previous [ 1 ] ] [ f ] [ x ] ] ] ] tail

        z1ef;

          // Apply [ 1 ] [ f ] [ x ] = Zero [ 1 ] [ x ] [ f [ Apply [ Previous [ 1 ] ] [ f ] [ x ] ] ]

          head;

          term-Apply;
          term-1;
          term-c; // Apply [ 1 ]
          f;
          term-c; // Apply [ 1 ] [ f ]
          x;
          term-c; // x = Apply [ 1 ] [ f ] [ x ]

          term-Zero;
          term-1;
          term-c; // Zero [ 1 ]
          x;
          term-c; // Zero [ 1 ] [ x ]
          f;
          term-Apply;
          term-Previous;
          term-1;
          term-c; // Previous [ 1 ]
          term-c; // Apply [ Previous [ 1 ] ]
          f;
          term-c; // Apply [ Previous [ 1 ] ] [ f ]
          x;
          term-c; // Apply [ Previous [ 1 ] ] [ f ] [ x ]
          term-c; // f [ Apply [ Previous [ 1 ] ] [ f ] [ x ] ]
          term-c; // y = Zero [ 1 ] [ x ] [ f [ Apply [ Previous [ 1 ] ] [ f ] [ x ] ] ]

          tail;

            term-1;     // n = 1
            f;          // f = f
            x;          // x = x
            df-Apply;   // Apply [ 1 ] [ f ] [ x ]

          apply1-e; // |- head Apply [ 1 ] [ f ] [ x ] tail

          df-eq;

        df-eq;

      false;

    df-eq;

  Apply0;

  };

  return |- head f [ x ] tail;
}

axiom term-Add() {
  return term Add;
}

// Add(m, n) = Apply(m, Next, n) = Next(... Next(Next(n)) ...) m times
axiom df-Add(term m, term n) {
  return |- Add [ m ] [ n ] = Apply [ m ] [ Next ] [ n ];
}

theorem z1ef() {
  do {

  // Zero [ 1 ] = First [ Pair [ F ] [ 0 ] ]

  term-Zero;
  word-t;
  word-l;
  word-c; // Zero [
  term-1;
  word-t;
  word-c; // Zero [ 1
  word-r;
  word-c; // Zero [ 1 ]
  word-eq;
  word-c; // Zero [ 1 ] =

  term-f; // x = F
  term-0; // y = 0

  word-null;

    // Zero [ 1 ] = First [ 1 ]

    term-Zero;
    word-t;
    word-l;
    word-c; // Zero [
    term-1;
    word-t;
    word-c; // Zero [ 1
    word-r;
    word-c; // Zero [ 1 ]
    word-eq;
    word-c; // Zero [ 1 ] = 
    term-first;
    word-t;
    word-c; // Zero [ 1 ] = First
    word-l;
    word-c; // Zero [ 1 ] = First [

    term-1; // x = 1

    term-pair;
    term-f;
    term-c; // Pair [ F ]
    term-0;
    term-c; // y = Pair [ F ] [ 0 ]

    word-r; // ]

    df-1;

      term-1;
      df-Zero;

    df-eq; // Zero [ 1 ] = First [ Pair [ F ] [ 0 ] ]

  first;
  };

  return |- Zero [ 1 ] = F;
}

theorem a1n1() {
  do {

  // Apply [ 1 ] [ Next ] [ 1 ] = Next [ Apply [ 0 ] [ Next ] [ 1 ] ]
  term-Apply;
  word-t;
  word-l;
  word-c; // Apply [
  term-1;
  word-t;
  word-c; // Apply [ 1
  word-r;
  word-c; // Apply [ 1 ]
  word-l;
  word-c; // Apply [ 1 ] [
  term-Next;
  word-t;
  word-c; // Apply [ 1 ] [ Next
  word-r;
  word-c; // Apply [ 1 ] [ Next ]
  word-l;
  word-c; // Apply [ 1 ] [ Next ] [
  term-1;
  word-t;
  word-c; // Apply [ 1 ] [ Next ] [ 1
  word-r;
  word-c; // Apply [ 1 ] [ Next ] [ 1 ]
  word-eq;
  word-c; // Apply [ 1 ] [ Next ] [ 1 ] =

  #;

  // ... continuing on Apply [ 1 ] [ Next ] [ 1 ] = Next [ Apply [ 0 ] [ Next ] [ 1 ] ]

  //term-Next;
  //word-t;
  //word-c; // Apply [ 1 ] [ Next ] [ 1 ] = Next
  //word-l;
  //word-c; // Apply [ 1 ] [ Next ] [ 1 ] = Next [

  //term-Apply;
  //term-0;
  //term-c; // Apply [ 0 ]
  //term-Next;
  //term-c; // Apply [ 0 ] [ Next ]
  //term-1;
  //term-c; // x = Apply [ 0 ] [ Next ] [ 1 ]

  //term-Zero;
  //term-0;
  //term-c; // Zero

  //word-r;

    // Apply [ 1 ] [ Next ] [ 1 ] = Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ] ]

    //@0;

    // ... continuing on Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ] ]

    term-Next;
    word-t;
    word-c; // Apply [ 1 ] [ Next ] [ 1 ] = Next
    word-l;
    word-c; // Apply [ 1 ] [ Next ] [ 1 ] = Next [
    term-Apply;
    word-t;
    word-c; // Apply [ 1 ] [ Next ] [ 1 ] = Next [ Apply
    word-l;
    word-c; // Apply [ 1 ] [ Next ] [ 1 ] = Next [ Apply [

    term-Previous;
    term-1;
    term-c; // x = Previous [ 1 ]

    term-0; // y = 0

    // ... continuing tail ] [ Next ] [ 1 ] ]

    word-r;
    word-l;
    word-c; // ] [
    term-Next;
    word-t;
    word-c; // ] [ Next
    word-r;
    word-c; // ] [ Next ]
    word-l;
    word-c; // ] [ Next ] [
    term-1;
    word-t;
    word-c; // ] [ Next ] [ 1
    word-r;
    word-c; // ] [ Next ] [ 1 ]
    word-r;
    word-c; // ] [ Next ] [ 1 ] ]

    p1e0;

      // Apply [ 1 ] [ Next ] [ 1 ] = F [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ] ] ]
      @0;

      term-1; // x = 1

      //  Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ] ]

      term-Next;
      term-Apply;
      term-Previous;
      term-1;
      term-c; // Previous [ 1 ]
      term-c; // Apply [ Previous [ 1 ] ]
      term-Next;
      term-c; // Apply [ Previous [ 1 ] ] [ Next ]
      term-1;
      term-c; // Apply [ Previous [ 1 ] ] [ Next ] [ 1 ]
      term-c; // Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ] ]
 
      word-null;

        // Apply [ 1 ] [ Next ] [ 1 ] = Zero [ 1 ] [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ] ] ]

        // head
        @0; // Use the previous result

        term-Zero;
        term-1;
        term-c; // x = Zero [ 1 ]

        term-f; // y = F

        // Apply [ 1 ] [ Next ] [ 1 ] = Zero [ 1 ] [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ] ] ]

        // tail
        word-l;
        term-1;
        word-t;
        word-c; // [ 1
        word-r;
        word-c; // [ 1 ]
        word-l;
        word-c; // [ 1 ] [
        term-Next;
        word-t;
        word-c; // [ 1 ] [ Next
        word-l;
        word-c; // [ 1 ] [ Next [
        term-Apply;
        word-t;
        word-c; // [ 1 ] [ Next [ Apply
        word-l;
        word-c; // [ 1 ] [ Next [ Apply [
        term-Previous;
        word-t;
        word-c; // [ 1 ] [ Next [ Apply [ Previous
        word-l;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [
        term-1;
        word-t;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1
        word-r;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1 ]
        word-r;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1 ] ]
        word-l;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [
        term-Next;
        word-t;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [ Next
        word-r;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [ Next ]
        word-l;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [ Next ] [
        term-1;
        word-t;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1
        word-r;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ]
        word-r;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ] ]
        word-r;
        word-c; // [ 1 ] [ Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ] ] ]

        z1ef;
    
          term-1;
          term-Next;
          term-1;
          df-Apply;

        df-eq;

      false;

    df-eq;
  };
  // return |- Apply [ 1 ] [ Next ] [ 1 ] = Next [ Apply [ Previous [ 1 ] ] [ Next ] [ 1 ] ];
  return |- Apply [ 1 ] [ Next ] [ 1 ] = Next [ Apply [ 0 ] [ Next ] [ 1 ] ];
}

//theorem 1p1e2() {
//
//  do {
//
//      term-1;
//      term-1;
//      df-Add; // Add [ 1 ] [ 1 ] = Apply [ 1 ] [ Next ] [ 1 ]
//
//  };
//
//  return |- Add [ 1 ] [ 1 ] = 2;
//}


    `;
    const {Compiler} = require("./../src/compiler.js");
    const {Verifier} = require("./../src/descent.js");
    const metamath = await new Compiler().compile(src);

    assertThat(new Verifier().verify(metamath) > 0).equalsTo(true);
    
  });
});

function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
