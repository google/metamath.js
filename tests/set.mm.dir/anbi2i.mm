include "wb.mm";
include "a1i.mm";
include "pm5.32i.mm";

theorem anbi2i(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume anbi.1: |- "( ph <-> ps )";





  do {
    wch;
    wph;
    wps;
    wph;
    wps;
    wb;
    wch;
    anbi.1;
    a1i;
    pm5.32i;
  };

  return '|-' "( ( ch /\\ ph ) <-> ( ch /\\ ps ) )";
}
