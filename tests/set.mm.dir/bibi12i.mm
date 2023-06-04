include "wb.mm";
include "bibi2i.mm";
include "bibi1i.mm";
include "bitri.mm";

theorem bibi12i(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th) {
  assume bibi2i.1: |- "( ph <-> ps )";
  assume bibi12i.2: |- "( ch <-> th )";





  do {
    wph;
    wch;
    wb;
    wph;
    wth;
    wb;
    wps;
    wth;
    wb;
    wch;
    wth;
    wph;
    bibi12i.2;
    bibi2i;
    wph;
    wps;
    wth;
    bibi2i.1;
    bibi1i;
    bitri;
  };

  return '|-' "( ( ph <-> ch ) <-> ( ps <-> th ) )";
}
