include "wo.mm";
include "wa.mm";
include "vneulem1.mm";
include "vneulem2.mm";
include "vneulem3.mm";
include "3tr.mm";

theorem vneulem4(wvu: $term$ u, wvw: $term$ w, wvx: $term$ x, wvy: $term$ y) {
  assume vneulem3.1: $|- ( ( x v y ) ^ ( u v w ) ) = 0$;





  do {
    wvx;
    wvy;
    wo;
    #;
    wvu;
    wo;
    #;
    wvw;
    wa;
    @1;
    wvu;
    wvw;
    wo;
    #;
    wvw;
    wa;
    wa;
    @0;
    @2;
    wa;
    wvu;
    wo;
    wvw;
    wa;
    wvu;
    wvw;
    wa;
    wvu;
    wvw;
    wvx;
    wvy;
    vneulem1;
    wvu;
    wvw;
    wvx;
    wvy;
    vneulem2;
    wvu;
    wvw;
    wvx;
    wvy;
    vneulem3.1;
    vneulem3;
    3tr;
  };

  return $|- ( ( ( x v y ) v u ) ^ w ) = ( u ^ w )$;
}
