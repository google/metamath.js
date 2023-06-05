include "bicomi.mm";
include "bitri.mm";

theorem bitr4i(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume bitr4i.1: |- "( ph <-> ps )";
  assume bitr4i.2: |- "( ch <-> ps )";





  do {
    wph;
    wps;
    wch;
    bitr4i.1;
    wch;
    wps;
    bitr4i.2;
    bicomi;
    bitri;
  };

  return |- "( ph <-> ch )";
}
