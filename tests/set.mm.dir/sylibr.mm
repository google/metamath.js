include "biimpri.mm";
include "syl.mm";

theorem sylibr(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume sylibr.1: |- "( ph -> ps )";
  assume sylibr.2: |- "( ch <-> ps )";





  do {
    wph;
    wps;
    wch;
    sylibr.1;
    wch;
    wps;
    sylibr.2;
    biimpri;
    syl;
  };

  return '|-' "( ph -> ch )";
}
