include "sylbb.mm";
include "sylbbr.mm";
include "impbii.mm";

theorem bitri(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume bitri.1: |- "( ph <-> ps )";
  assume bitri.2: |- "( ps <-> ch )";





  do {
    wph;
    wch;
    wph;
    wps;
    wch;
    bitri.1;
    bitri.2;
    sylbb;
    wph;
    wps;
    wch;
    bitri.1;
    bitri.2;
    sylbbr;
    impbii;
  };

  return |- "( ph <-> ch )";
}
