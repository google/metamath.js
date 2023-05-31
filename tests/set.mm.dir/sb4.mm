include "wsb.mm";
include "weq.mm";
include "wa.mm";
include "wex.mm";
include "wal.mm";
include "wn.mm";
include "wi.mm";
include "sb1.mm";
include "equs5.mm";
include "syl5ib.mm";

theorem sb4(wph: $wff$ ph, vx: $setvar$ x, vy: $setvar$ y) {





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
    wa;
    vx;
    wex;
    @0;
    vx;
    wal;
    wn;
    @0;
    wph;
    wi;
    vx;
    wal;
    wph;
    vx;
    vy;
    sb1;
    wph;
    vx;
    vy;
    equs5;
    syl5ib;
  };

  return $|-$ $( -. A. x x = y -> ( [ y / x ] ph -> A. x ( x = y -> ph ) ) )$;
}
