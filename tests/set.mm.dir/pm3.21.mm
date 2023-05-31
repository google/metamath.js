include "wa.mm";
include "id.mm";
include "expcom.mm";

theorem pm3.21(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wps;
    wph;
    wps;
    wph;
    wa;
    #;
    @0;
    id;
    expcom;
  };

  return $|-$ $( ph -> ( ps -> ( ps /\ ph ) ) )$;
}
