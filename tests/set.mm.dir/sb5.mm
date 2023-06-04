include "wsb.mm";
include "weq.mm";
include "wi.mm";
include "wal.mm";
include "wa.mm";
include "wex.mm";
include "sb6.mm";
include "sb56.mm";
include "bitr4i.mm";

theorem sb5(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {

  disjoint x y;



  do {
    wph;
    vx;
    vy;
    wsb;
    vx;
    vy;
    weq;
    #;
    wph;
    wi;
    vx;
    wal;
    @0;
    wph;
    wa;
    vx;
    wex;
    wph;
    vx;
    vy;
    sb6;
    wph;
    vx;
    vy;
    sb56;
    bitr4i;
  };

  return '|-' "( [ y / x ] ph <-> E. x ( x = y /\\ ph ) )";
}
