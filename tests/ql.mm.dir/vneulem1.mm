include "wo.mm";
include "wa.mm";
include "leor.mm";
include "leid.mm";
include "ler2an.mm";
include "lear.mm";
include "lebi.mm";
include "lan.mm";

theorem vneulem1(wvu: $term$ u, wvw: $term$ w, wvx: $term$ x, wvy: $term$ y) {





  do {
    wvw;
    wvu;
    wvw;
    wo;
    #;
    wvw;
    wa;
    #;
    wvx;
    wvy;
    wo;
    wvu;
    wo;
    wvw;
    @1;
    wvw;
    @0;
    wvw;
    wvw;
    wvu;
    leor;
    wvw;
    leid;
    ler2an;
    @0;
    wvw;
    lear;
    lebi;
    lan;
  };

  return $|- ( ( ( x v y ) v u ) ^ w ) = ( ( ( x v y ) v u ) ^ ( ( u v w ) ^ w ) )$;
}
