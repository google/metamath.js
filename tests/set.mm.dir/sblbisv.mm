include "wb.mm";
include "wsb.mm";
include "sbbiv.mm";
include "bibi2i.mm";
include "bitri.mm";

theorem sblbisv(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, vx: $setvar$ x, vy: $setvar$ y) {
  assume sblbisv.1: $|- ( [ y / x ] ph <-> ps )$;

  disjoint x y;



  do {
    wch;
    wph;
    wb;
    vx;
    vy;
    wsb;
    wch;
    vx;
    vy;
    wsb;
    #;
    wph;
    vx;
    vy;
    wsb;
    #;
    wb;
    @0;
    wps;
    wb;
    wch;
    wph;
    vx;
    vy;
    sbbiv;
    @1;
    wps;
    @0;
    sblbisv.1;
    bibi2i;
    bitri;
  };

  return $|-$ $( [ y / x ] ( ch <-> ph ) <-> ( [ y / x ] ch <-> ps ) )$;
}
