include "biimpri.mm";
include "sylibr.mm";

theorem sylbbr(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume sylbbr.1: |- "( ph <-> ps )";
  assume sylbbr.2: |- "( ps <-> ch )";





  do {
    wch;
    wps;
    wph;
    wps;
    wch;
    sylbbr.2;
    biimpri;
    sylbbr.1;
    sylibr;
  };

  return |- "( ch -> ph )";
}
