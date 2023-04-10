include "ke.mm";
include "kbr.mm";
include "ax-cb1.mm";
include "eqid.mm";
include "oveq123.mm";

theorem oveq(hal: $type$ al, hbe: $type$ be, hga: $type$ ga, ta: $term$ A, tb: $term$ B, tf: $term$ F, tr: $term$ R, ts: $term$ S) {
  assume oveq.1: $|- F : ( al -> ( be -> ga ) )$;
  assume oveq.2: $|- A : al$;
  assume oveq.3: $|- B : be$;
  assume oveq.4: $|- R |= [ F = S ]$;





  do {
    hal;
    hbe;
    hga;
    ta;
    tb;
    ta;
    tf;
    tr;
    ts;
    tb;
    oveq.1;
    oveq.2;
    oveq.3;
    oveq.4;
    hal;
    ta;
    tr;
    tf;
    ts;
    ke;
    kbr;
    tr;
    oveq.4;
    ax-cb1;
    #;
    oveq.2;
    eqid;
    hbe;
    tb;
    tr;
    @0;
    oveq.3;
    eqid;
    oveq123;
  };

  return $|- R |= [ [ A F B ] = [ A S B ] ]$;
}
