include "syl5bbr.mm";
include "syl6bb.mm";

theorem 3bitr3g(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th, wta: 'wff' ta) {
  assume 3bitr3g.1: |- "( ph -> ( ps <-> ch ) )";
  assume 3bitr3g.2: |- "( ps <-> th )";
  assume 3bitr3g.3: |- "( ch <-> ta )";





  do {
    wph;
    wth;
    wch;
    wta;
    wth;
    wps;
    wph;
    wch;
    3bitr3g.2;
    3bitr3g.1;
    syl5bbr;
    3bitr3g.3;
    syl6bb;
  };

  return '|-' "( ph -> ( th <-> ta ) )";
}
