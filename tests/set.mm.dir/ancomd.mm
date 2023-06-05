include "wa.mm";
include "ancom.mm";
include "sylib.mm";

theorem ancomd(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume ancomd.1: |- "( ph -> ( ps /\\ ch ) )";





  do {
    wph;
    wps;
    wch;
    wa;
    wch;
    wps;
    wa;
    ancomd.1;
    wps;
    wch;
    ancom;
    sylib;
  };

  return |- "( ph -> ( ch /\\ ps ) )";
}
