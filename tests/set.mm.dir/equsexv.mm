include "weq.mm";
include "wa.mm";
include "wex.mm";
include "pm5.32i.mm";
include "exbii.mm";
include "ax6ev.mm";
include "19.41.mm";
include "mpbiran.mm";
include "bitri.mm";

theorem equsexv(wph: wff ph, wps: wff ps, vx: setvar x, vy: setvar y) {
  assume equsalv.nf: |- "F/ x ps";
  assume equsalv.1: |- "( x = y -> ( ph <-> ps ) )";

  disjoint x y;



  do {
    vx;
    vy;
    weq;
    #;
    wph;
    wa;
    #;
    vx;
    wex;
    @0;
    wps;
    wa;
    #;
    vx;
    wex;
    #;
    wps;
    @1;
    @2;
    vx;
    @0;
    wph;
    wps;
    equsalv.1;
    pm5.32i;
    exbii;
    @3;
    @0;
    vx;
    wex;
    wps;
    vx;
    vy;
    ax6ev;
    @0;
    wps;
    vx;
    equsalv.nf;
    19.41;
    mpbiran;
    bitri;
  };

  return |- "( E. x ( x = y /\\ ph ) <-> ps )";
}
