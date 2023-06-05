include "wa.mm";
include "3expb.mm";
include "mpan.mm";

theorem mp3an1(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th) {
  assume mp3an1.1: |- "ph";
  assume mp3an1.2: |- "( ( ph /\\ ps /\\ ch ) -> th )";





  do {
    wph;
    wps;
    wch;
    wa;
    wth;
    mp3an1.1;
    wph;
    wps;
    wch;
    wth;
    mp3an1.2;
    3expb;
    mpan;
  };

  return |- "( ( ps /\\ ch ) -> th )";
}
