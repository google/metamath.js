include "wi.mm";
include "id.mm";
include "aleximi.mm";

theorem exim(wph: wff ph, wps: wff ps, vx: setvar x) {





  do {
    wph;
    wps;
    wi;
    #;
    wph;
    wps;
    vx;
    @0;
    id;
    aleximi;
  };

  return |- "( A. x ( ph -> ps ) -> ( E. x ph -> E. x ps ) )";
}
