include "wb.mm";
include "wi.mm";
include "wa.mm";
include "pm5.32.mm";
include "mpbi.mm";

theorem pm5.32i(wph: 'wff' ph, wps: 'wff' ps, wch: 'wff' ch) {
  assume pm5.32i.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wps;
    wch;
    wb;
    wi;
    wph;
    wps;
    wa;
    wph;
    wch;
    wa;
    wb;
    pm5.32i.1;
    wph;
    wps;
    wch;
    pm5.32;
    mpbi;
  };

  return '|-' "( ( ph /\\ ps ) <-> ( ph /\\ ch ) )";
}
