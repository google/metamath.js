include "syl.mm";

theorem 3syl(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th) {
  assume 3syl.1: $|- ( ph -> ps )$;
  assume 3syl.2: $|- ( ps -> ch )$;
  assume 3syl.3: $|- ( ch -> th )$;





  do {
    wph;
    wch;
    wth;
    wph;
    wps;
    wch;
    3syl.1;
    3syl.2;
    syl;
    3syl.3;
    syl;
  };

  return $|-$ $( ph -> th )$;
}
