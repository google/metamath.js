include "adantr.mm";
include "ancoms.mm";

theorem adantl(tr: term R, ts: term S, tt: term T) {
  assume adantr.1: |- "R |= T";
  assume adantr.2: |- "S : bool";





  do {
    tr;
    ts;
    tt;
    tr;
    ts;
    tt;
    adantr.1;
    adantr.2;
    adantr;
    ancoms;
  };

  return '|-' "( S , R ) |= T";
}
