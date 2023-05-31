include "wnf.mm";
include "wa.mm";
include "simpl.mm";
include "simpr.mm";
include "nfimd.mm";

theorem nfimt(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {





  do {
    wph;
    vx;
    wnf;
    #;
    wps;
    vx;
    wnf;
    #;
    wa;
    wph;
    wps;
    vx;
    @0;
    @1;
    simpl;
    @0;
    @1;
    simpr;
    nfimd;
  };

  return $|-$ $( ( F/ x ph /\ F/ x ps ) -> F/ x ( ph -> ps ) )$;
}
