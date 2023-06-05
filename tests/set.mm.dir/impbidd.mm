include "wi.mm";
include "wb.mm";
include "impbi.mm";
include "syl6c.mm";

theorem impbidd(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume impbidd.1: |- "( ph -> ( ps -> ( ch -> th ) ) )";
  assume impbidd.2: |- "( ph -> ( ps -> ( th -> ch ) ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    wi;
    wth;
    wch;
    wi;
    wch;
    wth;
    wb;
    impbidd.1;
    impbidd.2;
    wch;
    wth;
    impbi;
    syl6c;
  };

  return |- "( ph -> ( ps -> ( ch <-> th ) ) )";
}
