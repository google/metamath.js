include "wo.mm";
include "tb.mm";
include "wn.mm";
include "wa.mm";
include "oran.mm";
include "2bi.mm";
include "bi1.mm";

theorem ska2b(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvc;
    wo;
    #;
    wvb;
    wvc;
    wo;
    #;
    tb;
    wva;
    wn;
    wvc;
    wn;
    #;
    wa;
    wn;
    #;
    wvb;
    wn;
    @2;
    wa;
    wn;
    #;
    tb;
    @0;
    @3;
    @1;
    @4;
    wva;
    wvc;
    oran;
    wvb;
    wvc;
    oran;
    2bi;
    bi1;
  };

  return $|- ( ( ( a v c ) == ( b v c ) ) == ( ( a ' ^ c ' ) ' == ( b ' ^ c ' ) ' ) ) = 1$;
}
