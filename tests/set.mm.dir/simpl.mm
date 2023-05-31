include "id.mm";
include "adantr.mm";

theorem simpl(wph: $wff$ ph, wps: $wff$ ps) {





  do {
    wph;
    wph;
    wps;
    wph;
    id;
    adantr;
  };

  return $|-$ $( ( ph /\ ps ) -> ph )$;
}
