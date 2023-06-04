include "wb.mm";
include "a1i.mm";
include "pm5.74i.mm";

theorem imbi2i(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume imbi2i.1: |- "( ph <-> ps )";





  do {
    wch;
    wph;
    wps;
    wph;
    wps;
    wb;
    wch;
    imbi2i.1;
    a1i;
    pm5.74i;
  };

  return '|-' "( ( ch -> ph ) <-> ( ch -> ps ) )";
}
