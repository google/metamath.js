include "wa.mm";
include "pm3.21.mm";
include "simpl.mm";
include "impbid1.mm";

theorem iba(wph: 'wff' ph, wps: 'wff' ps) {





  do {
    wph;
    wps;
    wps;
    wph;
    wa;
    wph;
    wps;
    pm3.21;
    wps;
    wph;
    simpl;
    impbid1;
  };

  return '|-' "( ph -> ( ps <-> ( ps /\\ ph ) ) )";
}
