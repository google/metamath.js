include "orcd.mm";
include "orcomd.mm";

theorem olcd(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume orcd.1: |- "( ph -> ps )";





  do {
    wph;
    wps;
    wch;
    wph;
    wps;
    wch;
    orcd.1;
    orcd;
    orcomd;
  };

  return |- "( ph -> ( ch \\/ ps ) )";
}
