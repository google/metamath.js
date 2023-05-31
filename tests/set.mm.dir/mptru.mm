include "wtru.mm";
include "tru.mm";
include "ax-mp.mm";

theorem mptru(wph: $wff$ ph) {
  assume mptru.1: $|- ( T. -> ph )$;





  do {
    wtru;
    wph;
    tru;
    mptru.1;
    ax-mp;
  };

  return $|-$ $ph$;
}
