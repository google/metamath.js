include "wa.mm";
include "simpl.mm";
include "syl5.mm";

theorem adantrd(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume adantrd.1: |- "( ph -> ( ps -> ch ) )";





  do {
    wps;
    wth;
    wa;
    wps;
    wph;
    wch;
    wps;
    wth;
    simpl;
    adantrd.1;
    syl5;
  };

  return |- "( ph -> ( ( ps /\\ th ) -> ch ) )";
}
