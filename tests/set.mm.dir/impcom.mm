include "com12.mm";
include "imp.mm";

theorem impcom(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume imp.1: |- "( ph -> ( ps -> ch ) )";





  do {
    wps;
    wph;
    wch;
    wph;
    wps;
    wch;
    imp.1;
    com12;
    imp;
  };

  return |- "( ( ps /\\ ph ) -> ch )";
}
