include "biimpi.mm";
include "syl.mm";

theorem sylbi(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume sylbi.1: |- "( ph <-> ps )";
  assume sylbi.2: |- "( ps -> ch )";





  do {
    wph;
    wps;
    wch;
    wph;
    wps;
    sylbi.1;
    biimpi;
    sylbi.2;
    syl;
  };

  return '|-' "( ph -> ch )";
}
