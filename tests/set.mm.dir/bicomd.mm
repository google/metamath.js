include "wb.mm";
include "bicom.mm";
include "sylib.mm";

theorem bicomd(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume bicomd.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wps;
    wch;
    wb;
    wch;
    wps;
    wb;
    bicomd.1;
    wps;
    wch;
    bicom;
    sylib;
  };

  return |- "( ph -> ( ch <-> ps ) )";
}
