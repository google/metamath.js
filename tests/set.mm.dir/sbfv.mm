include "wnf.mm";
include "wsb.mm";
include "wb.mm";
include "sbftv.mm";
include "ax-mp.mm";

theorem sbfv(wph: $wff$ ph, vx: $setvar$ x, vy: $setvar$ y) {
  assume sbfv.1: $|- F/ x ph$;

  disjoint x y;



  do {
    wph;
    vx;
    wnf;
    wph;
    vx;
    vy;
    wsb;
    wph;
    wb;
    sbfv.1;
    wph;
    vx;
    vy;
    sbftv;
    ax-mp;
  };

  return $|-$ $( [ y / x ] ph <-> ph )$;
}
