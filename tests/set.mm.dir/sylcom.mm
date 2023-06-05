include "wi.mm";
include "a2i.mm";
include "syl.mm";

theorem sylcom(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume sylcom.1: |- "( ph -> ( ps -> ch ) )";
  assume sylcom.2: |- "( ps -> ( ch -> th ) )";





  do {
    wph;
    wps;
    wch;
    wi;
    wps;
    wth;
    wi;
    sylcom.1;
    wps;
    wch;
    wth;
    sylcom.2;
    a2i;
    syl;
  };

  return |- "( ph -> ( ps -> th ) )";
}
