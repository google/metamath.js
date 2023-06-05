include "syl5bir.mm";
include "syl6ib.mm";

theorem 3imtr3g(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th, wta: wff ta) {
  assume 3imtr3g.1: |- "( ph -> ( ps -> ch ) )";
  assume 3imtr3g.2: |- "( ps <-> th )";
  assume 3imtr3g.3: |- "( ch <-> ta )";





  do {
    wph;
    wth;
    wch;
    wta;
    wth;
    wps;
    wph;
    wch;
    3imtr3g.2;
    3imtr3g.1;
    syl5bir;
    3imtr3g.3;
    syl6ib;
  };

  return |- "( ph -> ( th -> ta ) )";
}
