include "wal.mm";
include "weq.mm";
include "wi.mm";
include "wsb.mm";
include "ala1.mm";
include "sb2v.mm";
include "syl.mm";

theorem stdpc4v(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {

  disjoint x y;



  do {
    wph;
    vx;
    wal;
    vx;
    vy;
    weq;
    #;
    wph;
    wi;
    vx;
    wal;
    wph;
    vx;
    vy;
    wsb;
    wph;
    @0;
    vx;
    ala1;
    wph;
    vx;
    vy;
    sb2v;
    syl;
  };

  return '|-' "( A. x ph -> [ y / x ] ph )";
}
