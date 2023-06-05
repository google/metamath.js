include "wa.mm";
include "w3a.mm";
include "df-3an.mm";
include "sylbir.mm";

theorem 3expa(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume 3exp.1: |- "( ( ph /\\ ps /\\ ch ) -> th )";





  do {
    wph;
    wps;
    wa;
    wch;
    wa;
    wph;
    wps;
    wch;
    w3a;
    wth;
    wph;
    wps;
    wch;
    df-3an;
    3exp.1;
    sylbir;
  };

  return |- "( ( ( ph /\\ ps ) /\\ ch ) -> th )";
}
