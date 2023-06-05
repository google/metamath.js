include "expcom.mm";
include "imp.mm";

theorem ancoms(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume ancoms.1: |- "( ( ph /\\ ps ) -> ch )";





  do {
    wps;
    wph;
    wch;
    wph;
    wps;
    wch;
    ancoms.1;
    expcom;
    imp;
  };

  return |- "( ( ps /\\ ph ) -> ch )";
}
