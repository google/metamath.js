include "bitri.mm";
include "bicomi.mm";

theorem bitr2i(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume bitr2i.1: |- "( ph <-> ps )";
  assume bitr2i.2: |- "( ps <-> ch )";





  do {
    wph;
    wch;
    wph;
    wps;
    wch;
    bitr2i.1;
    bitr2i.2;
    bitri;
    bicomi;
  };

  return '|-' "( ch <-> ph )";
}
