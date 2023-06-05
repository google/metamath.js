include "sylbi.mm";
include "sylibr.mm";

theorem 3imtr4i(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume 3imtr4.1: |- "( ph -> ps )";
  assume 3imtr4.2: |- "( ch <-> ph )";
  assume 3imtr4.3: |- "( th <-> ps )";





  do {
    wch;
    wps;
    wth;
    wch;
    wph;
    wps;
    3imtr4.2;
    3imtr4.1;
    sylbi;
    3imtr4.3;
    sylibr;
  };

  return |- "( ch -> th )";
}
