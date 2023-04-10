include "ke.mm";
include "weq.mm";
include "kc.mm";
include "ax-refl.mm";
include "a1i.mm";
include "dfov2.mm";

theorem eqid(hal: $type$ al, ta: $term$ A, tr: $term$ R) {
  assume eqid.1: $|- R : bool$;
  assume eqid.2: $|- A : al$;





  do {
    hal;
    hal;
    ta;
    ta;
    ke;
    tr;
    hal;
    weq;
    eqid.2;
    eqid.2;
    ke;
    ta;
    kc;
    ta;
    kc;
    tr;
    eqid.1;
    hal;
    ta;
    eqid.2;
    ax-refl;
    a1i;
    dfov2;
  };

  return $|- R |= [ A = A ]$;
}
