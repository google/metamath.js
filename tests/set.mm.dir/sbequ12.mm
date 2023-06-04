include "weq.mm";
include "wsb.mm";
include "sbequ1.mm";
include "sbequ2.mm";
include "impbid.mm";

theorem sbequ12(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {





  do {
    vx;
    vy;
    weq;
    wph;
    wph;
    vx;
    vy;
    wsb;
    wph;
    vx;
    vy;
    sbequ1;
    wph;
    vx;
    vy;
    sbequ2;
    impbid;
  };

  return '|-' "( x = y -> ( ph <-> [ y / x ] ph ) )";
}
