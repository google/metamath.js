include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wi5.mm";
include "wi3.mm";
include "leor.mm";
include "lelan.mm";
include "leror.mm";
include "df-i5.mm";
include "ax-a3.mm";
include "ax-r2.mm";
include "df-i3.mm";
include "ax-a2.mm";
include "le3tr1.mm";

theorem i5lei3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wn;
    #;
    wvb;
    wa;
    #;
    @1;
    wvb;
    wn;
    wa;
    #;
    wo;
    #;
    wo;
    #;
    wva;
    @1;
    wvb;
    wo;
    #;
    wa;
    #;
    @4;
    wo;
    #;
    wva;
    wvb;
    wi5;
    #;
    wva;
    wvb;
    wi3;
    #;
    @0;
    @7;
    @4;
    wvb;
    @6;
    wva;
    wvb;
    @1;
    leor;
    lelan;
    leror;
    @9;
    @0;
    @2;
    wo;
    @3;
    wo;
    @5;
    wva;
    wvb;
    df-i5;
    @0;
    @2;
    @3;
    ax-a3;
    ax-r2;
    @10;
    @4;
    @7;
    wo;
    @8;
    wva;
    wvb;
    df-i3;
    @4;
    @7;
    ax-a2;
    ax-r2;
    le3tr1;
  };

  return $|- ( a ->5 b ) =< ( a ->3 b )$;
}
