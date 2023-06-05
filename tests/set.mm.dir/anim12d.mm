include "wa.mm";
include "idd.mm";
include "syl2and.mm";

theorem anim12d(wph: wff ph, wps: wff ps, wch: wff ch, wth: wff th, wta: wff ta) {
  assume anim12d.1: |- "( ph -> ( ps -> ch ) )";
  assume anim12d.2: |- "( ph -> ( th -> ta ) )";





  do {
    wph;
    wps;
    wch;
    wth;
    wta;
    wch;
    wta;
    wa;
    #;
    anim12d.1;
    anim12d.2;
    wph;
    @0;
    idd;
    syl2and;
  };

  return |- "( ph -> ( ( ps /\\ th ) -> ( ch /\\ ta ) ) )";
}
