include "wa.mm";
include "id.mm";
include "ancoms.mm";

theorem pm3.22(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wps;
    wph;
    wps;
    wph;
    wa;
    #;
    @0;
    id;
    ancoms;
  };

  return $|-$ $( ( ph /\ ps ) -> ( ps /\ ph ) )$;
}
