include "kct.mm";
include "tim.mm";
include "kbr.mm";
include "ax-cb1.mm";
include "simpr.mm";
include "adantr.mm";
include "mpd.mm";

theorem imp(tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume imp.1: $|- S : bool$;
  assume imp.2: $|- T : bool$;
  assume imp.3: $|- R |= [ S ==> T ]$;





  do {
    tr;
    ts;
    kct;
    ts;
    tt;
    imp.2;
    tr;
    ts;
    ts;
    tt;
    tim;
    kbr;
    #;
    tr;
    imp.3;
    ax-cb1;
    imp.1;
    simpr;
    tr;
    ts;
    @0;
    imp.3;
    imp.1;
    adantr;
    mpd;
  };

  return $|- ( R , S ) |= T$;
}
