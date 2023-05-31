include "wi.mm";
include "id.mm";
include "con3d.mm";

theorem con3(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wi;
    #;
    wph;
    wps;
    @0;
    id;
    con3d;
  };

  return $|-$ $( ( ph -> ps ) -> ( -. ps -> -. ph ) )$;
}
