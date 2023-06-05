include "wa.mm";
include "jctild.mm";
include "syl6.mm";

theorem syl6an(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th, wta: wff ta) {
  assume syl6an.1: |- "( ph -> ps )";
  assume syl6an.2: |- "( ph -> ( ch -> th ) )";
  assume syl6an.3: |- "( ( ps /\\ th ) -> ta )";





  do {
    wph;
    wch;
    wps;
    wth;
    wa;
    wta;
    wph;
    wch;
    wth;
    wps;
    syl6an.2;
    syl6an.1;
    jctild;
    syl6an.3;
    syl6;
  };

  return |- "( ph -> ( ch -> ta ) )";
}
