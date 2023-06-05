include "wo.mm";
include "biimpi.mm";
include "orim2i.mm";
include "biimpri.mm";
include "impbii.mm";

theorem orbi2i(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume orbi2i.1: |- "( ph <-> ps )";





  do {
    wch;
    wph;
    wo;
    wch;
    wps;
    wo;
    wph;
    wps;
    wch;
    wph;
    wps;
    orbi2i.1;
    biimpi;
    orim2i;
    wps;
    wph;
    wch;
    wph;
    wps;
    orbi2i.1;
    biimpri;
    orim2i;
    impbii;
  };

  return |- "( ( ch \\/ ph ) <-> ( ch \\/ ps ) )";
}
