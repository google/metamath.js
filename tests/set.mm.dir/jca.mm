include "wa.mm";
include "pm3.2.mm";
include "sylc.mm";

theorem jca(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume jca.1: |- "( ph -> ps )";
  assume jca.2: |- "( ph -> ch )";





  do {
    wph;
    wps;
    wch;
    wps;
    wch;
    wa;
    jca.1;
    jca.2;
    wps;
    wch;
    pm3.2;
    sylc;
  };

  return '|-' "( ph -> ( ps /\\ ch ) )";
}
