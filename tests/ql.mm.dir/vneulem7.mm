include "wa.mm";
include "wo.mm";
include "wf.mm";
include "leao2.mm";
include "leao1.mm";
include "ler2an.mm";
include "lbtr.mm";
include "le0.mm";
include "lebi.mm";
include "ror.mm";
include "or0r.mm";
include "tr.mm";

theorem vneulem7(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume vneulem6.1: $|- ( ( a v b ) ^ ( c v d ) ) = 0$;





  do {
    wvc;
    wva;
    wa;
    #;
    wvb;
    wvd;
    wo;
    #;
    wo;
    wf;
    @1;
    wo;
    @1;
    @0;
    wf;
    @1;
    @0;
    wf;
    @0;
    wva;
    wvb;
    wo;
    #;
    wvc;
    wvd;
    wo;
    #;
    wa;
    wf;
    @0;
    @2;
    @3;
    wva;
    wvc;
    wvb;
    leao2;
    wvc;
    wva;
    wvd;
    leao1;
    ler2an;
    vneulem6.1;
    lbtr;
    @0;
    le0;
    lebi;
    ror;
    @1;
    or0r;
    tr;
  };

  return $|-$ $( ( c ^ a ) v ( b v d ) ) = ( b v d )$;
}
