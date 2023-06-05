include "wa.mm";
include "pm5.32i.mm";
include "ancom.mm";
include "3bitr4i.mm";

theorem pm5.32ri(wph: wff ph, wps: wff ps, wch: wff ch) {
  assume pm5.32i.1: |- "( ph -> ( ps <-> ch ) )";





  do {
    wph;
    wps;
    wa;
    wph;
    wch;
    wa;
    wps;
    wph;
    wa;
    wch;
    wph;
    wa;
    wph;
    wps;
    wch;
    pm5.32i.1;
    pm5.32i;
    wps;
    wph;
    ancom;
    wch;
    wph;
    ancom;
    3bitr4i;
  };

  return |- "( ( ps /\\ ph ) <-> ( ch /\\ ph ) )";
}
