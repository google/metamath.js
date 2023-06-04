include "ht.mm";
include "ke.mm";
include "kbr.mm";
include "ax-cb1.mm";
include "eqid.mm";
include "oveq123.mm";

theorem oveq12(hal: type al, hbe: type be, hga: type ga, ta: term A, tb: term B, tc: term C, tf: term F, tr: term R, tt: term T) {
  assume oveq.1: |- "F : ( al -> ( be -> ga ) )";
  assume oveq.2: |- "A : al";
  assume oveq.3: |- "B : be";
  assume oveq1.4: |- "R |= [ A = C ]";
  assume oveq12.5: |- "R |= [ B = T ]";





  do {
    hal;
    hbe;
    hga;
    ta;
    tb;
    tc;
    tf;
    tr;
    tf;
    tt;
    oveq.1;
    oveq.2;
    oveq.3;
    hal;
    hbe;
    hga;
    ht;
    ht;
    tf;
    tr;
    ta;
    tc;
    ke;
    kbr;
    tr;
    oveq1.4;
    ax-cb1;
    oveq.1;
    eqid;
    oveq1.4;
    oveq12.5;
    oveq123;
  };

  return '|-' "R |= [ [ A F B ] = [ C F T ] ]";
}
