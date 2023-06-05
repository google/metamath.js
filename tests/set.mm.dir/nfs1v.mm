include "wsb.mm";
include "weq.mm";
include "wi.mm";
include "wal.mm";
include "sb6.mm";
include "nfa1.mm";
include "nfxfr.mm";

theorem nfs1v(wph: wff ph, vx: setvar x, vy: setvar y) {

  disjoint x y;



  do {
    wph;
    vx;
    vy;
    wsb;
    vx;
    vy;
    weq;
    wph;
    wi;
    #;
    vx;
    wal;
    vx;
    wph;
    vx;
    vy;
    sb6;
    @0;
    vx;
    nfa1;
    nfxfr;
  };

  return |- "F/ x [ y / x ] ph";
}
