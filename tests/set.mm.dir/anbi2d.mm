include "wb.mm";
include "a1d.mm";
include "pm5.32d.mm";

theorem anbi2d(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume anbid.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wth;
    wps;
    wch;
    wph;
    wps;
    wch;
    wb;
    wth;
    anbid.1;
    a1d;
    pm5.32d;
  };

  return |- "( ph -> ( ( th /\\ ps ) <-> ( th /\\ ch ) ) )";
}
