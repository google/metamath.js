include "ancomd.mm";
include "simpld.mm";

theorem simprd(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume simprd.1: |- "( ph -> ( ps /\\ ch ) )";





  do {
    wph;
    wch;
    wps;
    wph;
    wps;
    wch;
    simprd.1;
    ancomd;
    simpld;
  };

  return |- "( ph -> ch )";
}
