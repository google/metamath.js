include "wa.mm";
include "pm3.2.mm";
include "a2i.mm";

theorem ancl(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wph;
    wps;
    wa;
    wph;
    wps;
    pm3.2;
    a2i;
  };

  return $|-$ $( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) )$;
}
