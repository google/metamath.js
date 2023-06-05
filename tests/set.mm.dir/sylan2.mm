include "adantl.mm";
include "syldan.mm";

theorem sylan2(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume sylan2.1: |- "( ph -> ch )";
  assume sylan2.2: |- "( ( ps /\\ ch ) -> th )";





  do {
    wps;
    wph;
    wch;
    wth;
    wph;
    wch;
    wps;
    sylan2.1;
    adantl;
    sylan2.2;
    syldan;
  };

  return |- "( ( ps /\\ ph ) -> th )";
}
