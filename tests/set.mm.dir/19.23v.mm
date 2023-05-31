include "wi.mm";
include "wal.mm";
include "wex.mm";
include "exim.mm";
include "ax5e.mm";
include "syl6.mm";
include "ax-5.mm";
include "imim2i.mm";
include "19.38.mm";
include "syl.mm";
include "impbii.mm";

theorem 19.23v(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {

  disjoint ps x;



  do {
    wph;
    wps;
    wi;
    vx;
    wal;
    #;
    wph;
    vx;
    wex;
    #;
    wps;
    wi;
    #;
    @0;
    @1;
    wps;
    vx;
    wex;
    wps;
    wph;
    wps;
    vx;
    exim;
    wps;
    vx;
    ax5e;
    syl6;
    @2;
    @1;
    wps;
    vx;
    wal;
    #;
    wi;
    @0;
    wps;
    @3;
    @1;
    wps;
    vx;
    ax-5;
    imim2i;
    wph;
    wps;
    vx;
    19.38;
    syl;
    impbii;
  };

  return $|-$ $( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) )$;
}
