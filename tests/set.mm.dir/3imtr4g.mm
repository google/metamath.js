include "syl5bi.mm";
include "syl6ibr.mm";

theorem 3imtr4g(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch, wth: $wff$ th, wta: $wff$ ta) {
  assume 3imtr4g.1: $|- ( ph -> ( ps -> ch ) )$;
  assume 3imtr4g.2: $|- ( th <-> ps )$;
  assume 3imtr4g.3: $|- ( ta <-> ch )$;





  do {
    wph;
    wth;
    wch;
    wta;
    wth;
    wps;
    wph;
    wch;
    3imtr4g.2;
    3imtr4g.1;
    syl5bi;
    3imtr4g.3;
    syl6ibr;
  };

  return $|-$ $( ph -> ( th -> ta ) )$;
}
