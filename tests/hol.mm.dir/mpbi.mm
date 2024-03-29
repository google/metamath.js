include "hb.mm";
include "ke.mm";
include "weq.mm";
include "ax-cb2.mm";
include "eqtypi.mm";
include "dfov1.mm";
include "ax-eqmp.mm";

theorem mpbi(ta: term A, tb: term B, tr: term R) {
  assume mpbi.1: |- "R |= A";
  assume mpbi.2: |- "R |= [ A = B ]";





  do {
    ta;
    tb;
    tr;
    mpbi.1;
    hb;
    hb;
    ta;
    tb;
    ke;
    tr;
    hb;
    weq;
    ta;
    tr;
    mpbi.1;
    ax-cb2;
    #;
    hb;
    ta;
    tb;
    tr;
    @0;
    mpbi.2;
    eqtypi;
    mpbi.2;
    dfov1;
    ax-eqmp;
  };

  return |- "R |= B";
}
