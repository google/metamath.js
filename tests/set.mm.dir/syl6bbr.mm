include "bicomi.mm";
include "syl6bb.mm";

theorem syl6bbr(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume syl6bbr.1: $|- ( ph -> ( ps <-> ch ) )$;
  assume syl6bbr.2: $|- ( th <-> ch )$;





  do {
    wph;
    wps;
    wch;
    wth;
    syl6bbr.1;
    wth;
    wch;
    syl6bbr.2;
    bicomi;
    syl6bb;
  };

  return $|-$ $( ph -> ( ps <-> th ) )$;
}
