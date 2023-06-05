include "weq.mm";
include "wal.mm";
include "wn.mm";
include "wa.mm";
include "wex.mm";
include "wi.mm";
include "nfna1.mm";
include "nfa1.mm";
include "axc15.mm";
include "impd.mm";
include "exlimd.mm";
include "equs4.mm";
include "impbid1.mm";

theorem equs5(wph: wff ph, vx: setvar x, vy: setvar y) {





  do {
    vx;
    vy;
    weq;
    #;
    vx;
    wal;
    wn;
    #;
    @0;
    wph;
    wa;
    #;
    vx;
    wex;
    @0;
    wph;
    wi;
    #;
    vx;
    wal;
    #;
    @1;
    @2;
    @4;
    vx;
    @0;
    vx;
    nfna1;
    @3;
    vx;
    nfa1;
    @1;
    @0;
    wph;
    @4;
    wph;
    vx;
    vy;
    axc15;
    impd;
    exlimd;
    wph;
    vx;
    vy;
    equs4;
    impbid1;
  };

  return |- "( -. A. x x = y -> ( E. x ( x = y /\\ ph ) <-> A. x ( x = y -> ph ) ) )";
}
