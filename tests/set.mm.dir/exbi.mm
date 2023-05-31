include "wb.mm";
include "id.mm";
include "alexbii.mm";

theorem exbi(wph: $wff$ ph, wps: $wff$ ps, vx: $setvar$ x) {





  do {
    wph;
    wps;
    wb;
    #;
    wph;
    wps;
    vx;
    @0;
    id;
    alexbii;
  };

  return $|-$ $( A. x ( ph <-> ps ) -> ( E. x ph <-> E. x ps ) )$;
}
