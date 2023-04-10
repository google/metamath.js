include "ke.mm";
include "kbr.mm";
include "ax-cb1.mm";
include "eqid.mm";
include "oveq12.mm";

theorem oveq2(hal: $type$ al, hbe: $type$ be, hga: $type$ ga, ta: $term$ A, tb: $term$ B, tf: $term$ F, tr: $term$ R, tt: $term$ T) {
  assume oveq.1: $|- F : ( al -> ( be -> ga ) )$;
  assume oveq.2: $|- A : al$;
  assume oveq.3: $|- B : be$;
  assume oveq2.4: $|- R |= [ B = T ]$;





  do {
    hal;
    hbe;
    hga;
    ta;
    tb;
    ta;
    tf;
    tr;
    tt;
    oveq.1;
    oveq.2;
    oveq.3;
    hal;
    ta;
    tr;
    tb;
    tt;
    ke;
    kbr;
    tr;
    oveq2.4;
    ax-cb1;
    oveq.2;
    eqid;
    oveq2.4;
    oveq12;
  };

  return $|-$ $R |= [ [ A F B ] = [ A F T ] ]$;
}
