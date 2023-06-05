include "biimpri.mm";
include "syl6.mm";

theorem syl6ibr(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume syl6ibr.1: |- "( ph -> ( ps -> ch ) )";
  assume syl6ibr.2: |- "( th <-> ch )";





  do {
    wph;
    wps;
    wch;
    wth;
    syl6ibr.1;
    wth;
    wch;
    syl6ibr.2;
    biimpri;
    syl6;
  };

  return |- "( ph -> ( ps -> th ) )";
}
