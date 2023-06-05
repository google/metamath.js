include "wi.mm";
include "a1i.mm";
include "sylcom.mm";

theorem syl6(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume syl6.1: |- "( ph -> ( ps -> ch ) )";
  assume syl6.2: |- "( ch -> th )";





  do {
    wph;
    wps;
    wch;
    wth;
    syl6.1;
    wch;
    wth;
    wi;
    wps;
    syl6.2;
    a1i;
    sylcom;
  };

  return |- "( ph -> ( ps -> th ) )";
}
