include "wa.mm";
include "simpr.mm";
include "syl5.mm";

theorem adantld(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume adantld.1: |- "( ph -> ( ps -> ch ) )";





  do {
    wth;
    wps;
    wa;
    wps;
    wph;
    wch;
    wth;
    wps;
    simpr;
    adantld.1;
    syl5;
  };

  return '|-' "( ph -> ( ( th /\\ ps ) -> ch ) )";
}
