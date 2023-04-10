include "wo.mm";
include "leror.mm";
include "lelor.mm";
include "letr.mm";

theorem le2or(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume le2.1: $|- a =< b$;
  assume le2.2: $|- c =< d$;





  do {
    wva;
    wvc;
    wo;
    wvb;
    wvc;
    wo;
    wvb;
    wvd;
    wo;
    wva;
    wvb;
    wvc;
    le2.1;
    leror;
    wvc;
    wvd;
    wvb;
    le2.2;
    lelor;
    letr;
  };

  return $|-$ $( a v c ) =< ( b v d )$;
}
