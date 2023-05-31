include "weq.mm";
include "wi.mm";
include "wal.mm";
include "wex.mm";
include "19.23v.mm";
include "pm5.74i.mm";
include "albii.mm";
include "ax6ev.mm";
include "a1bi.mm";
include "3bitr4i.mm";

theorem equsalvw(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x, vy: $setvar$ y) {
  assume equsalvw.1: $|- ( x = y -> ( ph <-> ps ) )$;

  disjoint x y;
  disjoint ps x;



  do {
    vx;
    vy;
    weq;
    #;
    wps;
    wi;
    #;
    vx;
    wal;
    @0;
    vx;
    wex;
    #;
    wps;
    wi;
    @0;
    wph;
    wi;
    #;
    vx;
    wal;
    wps;
    @0;
    wps;
    vx;
    19.23v;
    @3;
    @1;
    vx;
    @0;
    wph;
    wps;
    equsalvw.1;
    pm5.74i;
    albii;
    @2;
    wps;
    vx;
    vy;
    ax6ev;
    a1bi;
    3bitr4i;
  };

  return $|-$ $( A. x ( x = y -> ph ) <-> ps )$;
}
