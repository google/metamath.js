include "cc.mm";
include "wcel.mm";
include "caddc.mm";
include "co.mm";
include "addcl.mm";
include "mp2an.mm";

theorem addcli(cA: $class$ A, cB: $class$ B) {
  assume axi.1: $|- A e. CC$;
  assume axi.2: $|- B e. CC$;





  do {
    cA;
    cc;
    wcel;
    cB;
    cc;
    wcel;
    cA;
    cB;
    caddc;
    co;
    cc;
    wcel;
    axi.1;
    axi.2;
    cA;
    cB;
    addcl;
    mp2an;
  };

  return $|-$ $( A + B ) e. CC$;
}
