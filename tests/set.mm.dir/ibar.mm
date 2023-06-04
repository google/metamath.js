include "wa.mm";
include "pm3.2.mm";
include "simpr.mm";
include "impbid1.mm";

theorem ibar(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wps;
    wph;
    wps;
    wa;
    wph;
    wps;
    pm3.2;
    wph;
    wps;
    simpr;
    impbid1;
  };

  return '|-' "( ph -> ( ps <-> ( ph /\\ ps ) ) )";
}
