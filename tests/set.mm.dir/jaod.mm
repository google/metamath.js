include "wo.mm";
include "wi.mm";
include "com12.mm";
include "jaoi.mm";

theorem jaod(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume jaod.1: |- "( ph -> ( ps -> ch ) )";
  assume jaod.2: |- "( ph -> ( th -> ch ) )";





  do {
    wps;
    wth;
    wo;
    wph;
    wch;
    wps;
    wph;
    wch;
    wi;
    wth;
    wph;
    wps;
    wch;
    jaod.1;
    com12;
    wph;
    wth;
    wch;
    jaod.2;
    com12;
    jaoi;
    com12;
  };

  return |- "( ph -> ( ( ps \\/ th ) -> ch ) )";
}
