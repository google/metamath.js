include "bitr3i.mm";
include "bitri.mm";

theorem 3bitr3i(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume 3bitr3i.1: |- "( ph <-> ps )";
  assume 3bitr3i.2: |- "( ph <-> ch )";
  assume 3bitr3i.3: |- "( ps <-> th )";





  do {
    wch;
    wps;
    wth;
    wch;
    wph;
    wps;
    3bitr3i.2;
    3bitr3i.1;
    bitr3i;
    3bitr3i.3;
    bitri;
  };

  return |- "( ch <-> th )";
}
