include "biimpd.mm";
include "syl5.mm";

theorem syl5ib(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume syl5ib.1: |- "( ph -> ps )";
  assume syl5ib.2: |- "( ch -> ( ps <-> th ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    syl5ib.1;
    wch;
    wps;
    wth;
    syl5ib.2;
    biimpd;
    syl5;
  };

  return '|-' "( ch -> ( ph -> th ) )";
}
