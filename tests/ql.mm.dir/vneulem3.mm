include "wo.mm";
include "wa.mm";
include "wf.mm";
include "ror.mm";
include "or0r.mm";
include "tr.mm";
include "ran.mm";

theorem vneulem3(wvu: $term$ u, wvw: $term$ w, wvx: $term$ x, wvy: $term$ y) {
  assume vneulem3.1: $|- ( ( x v y ) ^ ( u v w ) ) = 0$;





  do {
    wvx;
    wvy;
    wo;
    wvu;
    wvw;
    wo;
    wa;
    #;
    wvu;
    wo;
    #;
    wvu;
    wvw;
    @1;
    wf;
    wvu;
    wo;
    wvu;
    @0;
    wf;
    wvu;
    vneulem3.1;
    ror;
    wvu;
    or0r;
    tr;
    ran;
  };

  return $|- ( ( ( ( x v y ) ^ ( u v w ) ) v u ) ^ w ) = ( u ^ w )$;
}
