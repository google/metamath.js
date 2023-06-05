include "biimpi.mm";
include "syl.mm";

theorem sylib(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume sylib.1: |- "( ph -> ps )";
  assume sylib.2: |- "( ps <-> ch )";





  do {
    wph;
    wps;
    wch;
    sylib.1;
    wps;
    wch;
    sylib.2;
    biimpi;
    syl;
  };

  return |- "( ph -> ch )";
}
