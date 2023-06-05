include "3syl.mm";
include "syl.mm";

theorem 4syl(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th, wta: wff ta) {
  assume 4syl.1: |- "( ph -> ps )";
  assume 4syl.2: |- "( ps -> ch )";
  assume 4syl.3: |- "( ch -> th )";
  assume 4syl.4: |- "( th -> ta )";





  do {
    wph;
    wth;
    wta;
    wph;
    wps;
    wch;
    wth;
    4syl.1;
    4syl.2;
    4syl.3;
    3syl;
    4syl.4;
    syl;
  };

  return |- "( ph -> ta )";
}
