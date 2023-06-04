include "syl5bb.mm";
include "syl6bbr.mm";

theorem 3bitr4g(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th, wta: 'wff' ta) {
  assume 3bitr4g.1: |- "( ph -> ( ps <-> ch ) )";
  assume 3bitr4g.2: |- "( th <-> ps )";
  assume 3bitr4g.3: |- "( ta <-> ch )";





  do {
    wph;
    wth;
    wch;
    wta;
    wth;
    wps;
    wph;
    wch;
    3bitr4g.2;
    3bitr4g.1;
    syl5bb;
    3bitr4g.3;
    syl6bbr;
  };

  return '|-' "( ph -> ( th <-> ta ) )";
}
