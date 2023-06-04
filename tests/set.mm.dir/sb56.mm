include "weq.mm";
include "wi.mm";
include "wal.mm";
include "nfa1.mm";
include "ax12v2.mm";
include "sp.mm";
include "com12.mm";
include "impbid.mm";
include "equsexv.mm";

theorem sb56(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {

  disjoint x y;



  do {
    wph;
    vx;
    vy;
    weq;
    #;
    wph;
    wi;
    #;
    vx;
    wal;
    #;
    vx;
    vy;
    @1;
    vx;
    nfa1;
    @0;
    wph;
    @2;
    wph;
    vx;
    vy;
    ax12v2;
    @2;
    @0;
    wph;
    @1;
    vx;
    sp;
    com12;
    impbid;
    equsexv;
  };

  return '|-' "( E. x ( x = y /\\ ph ) <-> A. x ( x = y -> ph ) )";
}
