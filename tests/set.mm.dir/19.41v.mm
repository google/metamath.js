include "wa.mm";
include "wex.mm";
include "19.40.mm";
include "ax5e.mm";
include "anim2i.mm";
include "syl.mm";
include "pm3.21.mm";
include "eximdv.mm";
include "impcom.mm";
include "impbii.mm";

theorem 19.41v(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {

  disjoint ps x;



  do {
    wph;
    wps;
    wa;
    #;
    vx;
    wex;
    #;
    wph;
    vx;
    wex;
    #;
    wps;
    wa;
    #;
    @1;
    @2;
    wps;
    vx;
    wex;
    #;
    wa;
    @3;
    wph;
    wps;
    vx;
    19.40;
    @4;
    wps;
    @2;
    wps;
    vx;
    ax5e;
    anim2i;
    syl;
    wps;
    @2;
    @1;
    wps;
    wph;
    @0;
    vx;
    wps;
    wph;
    pm3.21;
    eximdv;
    impcom;
    impbii;
  };

  return $|-$ $( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) )$;
}
