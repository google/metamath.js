include "tne.mm";
include "kc.mm";
include "tfal.mm";
include "tim.mm";
include "kbr.mm";
include "kct.mm";
include "wfal.mm";
include "hb.mm";
include "wnot.mm";
include "wc.mm";
include "simpl.mm";
include "simpr.mm";
include "ke.mm";
include "ax-cb1.mm";
include "notval.mm";
include "a1i.mm";
include "mpbi.mm";
include "mpd.mm";
include "ex.mm";
include "mpbir.mm";

theorem notnot1(ta: $term$ A) {
  assume notval2.1: $|- A : bool$;





  do {
    tne;
    ta;
    kc;
    #;
    tfal;
    tim;
    kbr;
    #;
    tne;
    @0;
    kc;
    #;
    ta;
    ta;
    @0;
    tfal;
    ta;
    @0;
    kct;
    #;
    ta;
    tfal;
    wfal;
    ta;
    @0;
    notval2.1;
    hb;
    hb;
    tne;
    ta;
    wnot;
    notval2.1;
    wc;
    #;
    simpl;
    #;
    @0;
    ta;
    tfal;
    tim;
    kbr;
    #;
    @3;
    ta;
    @0;
    notval2.1;
    @4;
    simpr;
    @0;
    @6;
    ke;
    kbr;
    @3;
    ta;
    @3;
    @5;
    ax-cb1;
    ta;
    notval2.1;
    notval;
    a1i;
    mpbi;
    mpd;
    ex;
    @2;
    @1;
    ke;
    kbr;
    ta;
    notval2.1;
    @0;
    @4;
    notval;
    a1i;
    mpbir;
  };

  return $|-$ $A |= ( ~ ( ~ A ) )$;
}
