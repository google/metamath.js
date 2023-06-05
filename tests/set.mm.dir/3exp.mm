include "3expa.mm";
include "exp31.mm";

theorem 3exp(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume 3exp.1: |- "( ( ph /\\ ps /\\ ch ) -> th )";





  do {
    wph;
    wps;
    wch;
    wth;
    wph;
    wps;
    wch;
    wth;
    3exp.1;
    3expa;
    exp31;
  };

  return |- "( ph -> ( ps -> ( ch -> th ) ) )";
}
