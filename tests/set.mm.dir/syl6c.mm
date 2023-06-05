include "wi.mm";
include "syl6.mm";
include "mpdd.mm";

theorem syl6c(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th, wta: wff ta) {
  assume syl6c.1: |- "( ph -> ( ps -> ch ) )";
  assume syl6c.2: |- "( ph -> ( ps -> th ) )";
  assume syl6c.3: |- "( ch -> ( th -> ta ) )";





  do {
    wph;
    wps;
    wth;
    wta;
    syl6c.2;
    wph;
    wps;
    wch;
    wth;
    wta;
    wi;
    syl6c.1;
    syl6c.3;
    syl6;
    mpdd;
  };

  return |- "( ph -> ( ps -> ta ) )";
}
