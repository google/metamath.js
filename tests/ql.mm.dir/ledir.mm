include "wa.mm";
include "wo.mm";
include "ledi.mm";
include "ancom.mm";
include "2or.mm";
include "le3tr1.mm";

theorem ledir(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wvc;
    wa;
    #;
    wo;
    wva;
    wvb;
    wvc;
    wo;
    #;
    wa;
    wvb;
    wva;
    wa;
    #;
    wvc;
    wva;
    wa;
    #;
    wo;
    @2;
    wva;
    wa;
    wva;
    wvb;
    wvc;
    ledi;
    @3;
    @0;
    @4;
    @1;
    wvb;
    wva;
    ancom;
    wvc;
    wva;
    ancom;
    2or;
    @2;
    wva;
    ancom;
    le3tr1;
  };

  return $|- ( ( b ^ a ) v ( c ^ a ) ) =< ( ( b v c ) ^ a )$;
}
