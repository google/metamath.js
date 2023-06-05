include "3exp.mm";
include "imp32.mm";

theorem 3expb(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
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
    3exp;
    imp32;
  };

  return |- "( ( ph /\\ ( ps /\\ ch ) ) -> th )";
}
