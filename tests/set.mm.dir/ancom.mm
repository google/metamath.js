include "wa.mm";
include "pm3.22.mm";
include "impbii.mm";

theorem ancom(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wa;
    wps;
    wph;
    wa;
    wph;
    wps;
    pm3.22;
    wps;
    wph;
    pm3.22;
    impbii;
  };

  return $|-$ $( ( ph /\ ps ) <-> ( ps /\ ph ) )$;
}
