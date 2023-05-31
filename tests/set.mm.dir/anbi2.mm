include "wb.mm";
include "id.mm";
include "anbi2d.mm";

theorem anbi2(wph: $wff$ ph, wps: $wff$ ps, wch: $wff$ ch) {





  do {
    wph;
    wps;
    wb;
    #;
    wph;
    wps;
    wch;
    @0;
    id;
    anbi2d;
  };

  return $|-$ $( ( ph <-> ps ) -> ( ( ch /\ ph ) <-> ( ch /\ ps ) ) )$;
}
