include "wi.mm";
include "id.mm";
include "com12.mm";

theorem pm2.27(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wps;
    wi;
    #;
    wph;
    wps;
    @0;
    id;
    com12;
  };

  return $|-$ $( ph -> ( ( ph -> ps ) -> ps ) )$;
}
