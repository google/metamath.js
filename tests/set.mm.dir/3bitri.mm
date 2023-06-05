include "bitri.mm";

theorem 3bitri(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume 3bitri.1: |- "( ph <-> ps )";
  assume 3bitri.2: |- "( ps <-> ch )";
  assume 3bitri.3: |- "( ch <-> th )";





  do {
    wph;
    wps;
    wth;
    3bitri.1;
    wps;
    wch;
    wth;
    3bitri.2;
    3bitri.3;
    bitri;
    bitri;
  };

  return |- "( ph <-> th )";
}
