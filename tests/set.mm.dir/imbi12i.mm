include "wb.mm";
include "wi.mm";
include "imbi12.mm";
include "mp2.mm";

theorem imbi12i(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume imbi12i.1: |- "( ph <-> ps )";
  assume imbi12i.2: |- "( ch <-> th )";





  do {
    wph;
    wps;
    wb;
    wch;
    wth;
    wb;
    wph;
    wch;
    wi;
    wps;
    wth;
    wi;
    wb;
    imbi12i.1;
    imbi12i.2;
    wph;
    wps;
    wch;
    wth;
    imbi12;
    mp2;
  };

  return '|-' "( ( ph -> ch ) <-> ( ps -> th ) )";
}
