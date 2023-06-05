include "wb.mm";
include "wsb.mm";
include "weq.mm";
include "equsb1v.mm";
include "sbimi.mm";
include "ax-mp.mm";
include "sbfv.mm";
include "sblbisv.mm";
include "mpbi.mm";

theorem sbiev(wph: wff ph, wps: wff ps, vx: setvar x, vy: setvar y) {
  assume sbiev.1: |- "F/ x ps";
  assume sbiev.2: |- "( x = y -> ( ph <-> ps ) )";

  disjoint x y;



  do {
    wph;
    wps;
    wb;
    #;
    vx;
    vy;
    wsb;
    #;
    wph;
    vx;
    vy;
    wsb;
    wps;
    wb;
    vx;
    vy;
    weq;
    #;
    vx;
    vy;
    wsb;
    @1;
    vx;
    vy;
    equsb1v;
    @2;
    @0;
    vx;
    vy;
    sbiev.2;
    sbimi;
    ax-mp;
    wps;
    wps;
    wph;
    vx;
    vy;
    wps;
    vx;
    vy;
    sbiev.1;
    sbfv;
    sblbisv;
    mpbi;
  };

  return |- "( [ y / x ] ph <-> ps )";
}
