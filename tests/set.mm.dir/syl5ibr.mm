include "bicomd.mm";
include "syl5ib.mm";

theorem syl5ibr(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume syl5ibr.1: |- "( ph -> th )";
  assume syl5ibr.2: |- "( ch -> ( ps <-> th ) )";





  do {
    wph;
    wth;
    wch;
    wps;
    syl5ibr.1;
    wch;
    wps;
    wth;
    syl5ibr.2;
    bicomd;
    syl5ib;
  };

  return '|-' "( ch -> ( ph -> ps ) )";
}
