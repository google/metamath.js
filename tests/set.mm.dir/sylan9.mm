include "wi.mm";
include "syl9.mm";
include "imp.mm";

theorem sylan9(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th, wta: wff ta) {
  assume sylan9.1: |- "( ph -> ( ps -> ch ) )";
  assume sylan9.2: |- "( th -> ( ch -> ta ) )";





  do {
    wph;
    wth;
    wps;
    wta;
    wi;
    wph;
    wps;
    wch;
    wth;
    wta;
    sylan9.1;
    sylan9.2;
    syl9;
    imp;
  };

  return |- "( ( ph /\\ th ) -> ( ps -> ta ) )";
}
