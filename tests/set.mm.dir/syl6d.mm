include "wi.mm";
include "a1d.mm";
include "syldd.mm";

theorem syl6d(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th, wta: wff ta) {
  assume syl6d.1: |- "( ph -> ( ps -> ( ch -> th ) ) )";
  assume syl6d.2: |- "( ph -> ( th -> ta ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    wta;
    syl6d.1;
    wph;
    wth;
    wta;
    wi;
    wps;
    syl6d.2;
    a1d;
    syldd;
  };

  return |- "( ph -> ( ps -> ( ch -> ta ) ) )";
}
