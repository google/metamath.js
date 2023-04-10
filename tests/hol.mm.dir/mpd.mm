include "tan.mm";
include "kbr.mm";
include "kct.mm";
include "tim.mm";
include "ke.mm";
include "ax-cb1.mm";
include "ax-cb2.mm";
include "imval.mm";
include "a1i.mm";
include "mpbi.mm";
include "mpbir.mm";
include "dfan2.mm";
include "simprd.mm";

theorem mpd(tr: $term$ R, ts: $term$ S, tt: $term$ T) {
  assume mp.1: $|- T : bool$;
  assume mp.2: $|- R |= S$;
  assume mp.3: $|- R |= [ S ==> T ]$;





  do {
    tr;
    ts;
    tt;
    ts;
    tt;
    tan;
    kbr;
    #;
    ts;
    tt;
    kct;
    #;
    tr;
    ts;
    @0;
    tr;
    mp.2;
    ts;
    tt;
    tim;
    kbr;
    #;
    @0;
    ts;
    ke;
    kbr;
    #;
    tr;
    mp.3;
    @2;
    @3;
    ke;
    kbr;
    tr;
    ts;
    tr;
    mp.2;
    ax-cb1;
    #;
    ts;
    tt;
    ts;
    tr;
    mp.2;
    ax-cb2;
    #;
    mp.1;
    imval;
    a1i;
    mpbi;
    mpbir;
    @0;
    @1;
    ke;
    kbr;
    tr;
    @4;
    ts;
    tt;
    @5;
    mp.1;
    dfan2;
    a1i;
    mpbi;
    simprd;
  };

  return $|- R |= T$;
}
