include "kct.mm";
include "ax-cb1.mm";
include "simpl.mm";
include "syl.mm";

theorem adantr(tr: term R, ts: term S, tt: term T) {
  assume adantr.1: |- "R |= T";
  assume adantr.2: |- "S : bool";





  do {
    tr;
    ts;
    kct;
    tr;
    tt;
    tr;
    ts;
    tt;
    tr;
    adantr.1;
    ax-cb1;
    adantr.2;
    simpl;
    adantr.1;
    syl;
  };

  return |- "( R , S ) |= T";
}
