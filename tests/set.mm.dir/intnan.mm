include "wa.mm";
include "simpr.mm";
include "mto.mm";

theorem intnan(wph: 'wff' ph, wps: 'wff' ps) {
  assume intnan.1: |- "-. ph";





  do {
    wps;
    wph;
    wa;
    wph;
    intnan.1;
    wps;
    wph;
    simpr;
    mto;
  };

  return '|-' "-. ( ps /\\ ph )";
}
