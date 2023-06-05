include "bicomi.mm";
include "bitri.mm";

theorem bitr3i(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume bitr3i.1: |- "( ps <-> ph )";
  assume bitr3i.2: |- "( ps <-> ch )";





  do {
    wph;
    wps;
    wch;
    wps;
    wph;
    bitr3i.1;
    bicomi;
    bitr3i.2;
    bitri;
  };

  return |- "( ph <-> ch )";
}
