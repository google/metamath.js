include "wsb.mm";
include "weq.mm";
include "wa.mm";
include "wex.mm";
include "wi.mm";
include "wal.mm";
include "sb1.mm";
include "sb56.mm";
include "sylib.mm";

theorem sb4v(wph: $wff$ ph, vx: $setvar$ x, vy: $setvar$ y) {

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
    wa;
    vx;
    wex;
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
    sb56;
    sylib;
  };

  return $|-$ $( [ y / x ] ph -> A. x ( x = y -> ph ) )$;
}
