include "wa.mm";
include "wex.mm";
include "exsimpl.mm";
include "exsimpr.mm";
include "jca.mm";

theorem 19.40(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {





  do {
    wph;
    wps;
    wa;
    vx;
    wex;
    wph;
    vx;
    wex;
    wps;
    vx;
    wex;
    wph;
    wps;
    vx;
    exsimpl;
    wph;
    wps;
    vx;
    exsimpr;
    jca;
  };

  return $|-$ $( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) )$;
}
