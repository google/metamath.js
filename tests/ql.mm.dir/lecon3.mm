include "wn.mm";
include "lecon.mm";
include "lecon2.mm";
include "lecon1.mm";

theorem lecon3(wva: $term$ a, wvb: $term$ b) {
  assume lecon3.1: $|- a =< b '$;





  do {
    wva;
    wn;
    #;
    wvb;
    wvb;
    wn;
    #;
    @0;
    wva;
    @1;
    lecon3.1;
    lecon;
    lecon2;
    lecon1;
  };

  return $|- b =< a '$;
}
