include "hb.mm";
include "tv.mm";
include "ax-cb1.mm";
include "wv.mm";
include "ax-17.mm";
include "ke.mm";
include "kbr.mm";
include "eqid.mm";
include "ax-inst.mm";

theorem insti(hal: type al, vx: var x, vy: var y, ta: term A, tb: term B, tc: term C, tr: term R) {
  assume insti.1: |- "C : al";
  assume insti.2: |- "B : bool";
  assume insti.3: |- "R |= A";
  assume insti.4: |- "T. |= [ ( \\ x : al . B y : al ) = B ]";
  assume insti.5: |- "[ x : al = C ] |= [ A = B ]";

  disjoint x y;
  disjoint R x;
  disjoint R y;
  disjoint B y;



  do {
    hal;
    vx;
    vy;
    ta;
    tb;
    tc;
    tr;
    tr;
    insti.3;
    insti.4;
    hal;
    hb;
    vx;
    tr;
    hal;
    vy;
    tv;
    ta;
    tr;
    insti.3;
    ax-cb1;
    #;
    hal;
    vy;
    wv;
    ax-17;
    insti.5;
    hb;
    tr;
    hal;
    vx;
    tv;
    tc;
    ke;
    kbr;
    #;
    ta;
    tb;
    ke;
    kbr;
    @1;
    insti.5;
    ax-cb1;
    @0;
    eqid;
    ax-inst;
  };

  return '|-' "R |= B";
}
