include "wi.mm";
include "wa.mm";
include "com12.mm";
include "ex.mm";

theorem expdcom(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume expd.1: |- "( ph -> ( ( ps /\\ ch ) -> th ) )";





  do {
    wps;
    wch;
    wph;
    wth;
    wi;
    wph;
    wps;
    wch;
    wa;
    wth;
    expd.1;
    com12;
    ex;
  };

  return |- "( ps -> ( ch -> ( ph -> th ) ) )";
}
