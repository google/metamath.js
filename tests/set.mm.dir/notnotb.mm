include "wn.mm";
include "notnot.mm";
include "notnotr.mm";
include "impbii.mm";

theorem notnotb(wph: $wff$ ph) {





  do {
    wph;
    wph;
    wn;
    wn;
    wph;
    notnot;
    wph;
    notnotr;
    impbii;
  };

  return $|-$ $( ph <-> -. -. ph )$;
}
