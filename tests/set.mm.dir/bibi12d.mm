include "wb.mm";
include "bibi1d.mm";
include "bibi2d.mm";
include "bitrd.mm";

theorem bibi12d(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch, wth: 'wff' th, wta: 'wff' ta) {
  assume imbi12d.1: |- "( ph -> ( ps <-> ch ) )";
  assume imbi12d.2: |- "( ph -> ( th <-> ta ) )";





  do {
    wph;
    wps;
    wth;
    wb;
    wch;
    wth;
    wb;
    wch;
    wta;
    wb;
    wph;
    wps;
    wch;
    wth;
    imbi12d.1;
    bibi1d;
    wph;
    wth;
    wta;
    wch;
    imbi12d.2;
    bibi2d;
    bitrd;
  };

  return '|-' "( ph -> ( ( ps <-> th ) <-> ( ch <-> ta ) ) )";
}
