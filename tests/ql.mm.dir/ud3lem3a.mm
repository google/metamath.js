include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "ud3lem0c.mm";
include "lea.mm";
include "lear.mm";
include "letr.mm";
include "bltr.mm";
include "df2le2.mm";

theorem ud3lem3a(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi3;
    wn;
    #;
    wva;
    wvb;
    wo;
    #;
    @0;
    wva;
    wvb;
    wn;
    #;
    wo;
    #;
    @1;
    wa;
    #;
    wva;
    wn;
    wva;
    @2;
    wa;
    wo;
    #;
    wa;
    #;
    @1;
    wva;
    wvb;
    ud3lem0c;
    @6;
    @4;
    @1;
    @4;
    @5;
    lea;
    @3;
    @1;
    lear;
    letr;
    bltr;
    df2le2;
  };

  return $|- ( ( a ->3 b ) ' ^ ( a v b ) ) = ( a ->3 b ) '$;
}
