include "wi2.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "ud2lem0c.mm";
include "lea.mm";
include "bltr.mm";
include "ax-oal4.mm";
include "id.mm";
include "oa4v3v.mm";
include "oal42.mm";
include "oa23.mm";

theorem oa43v(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
    wva;
    wvc;
    wvb;
    wva;
    wvc;
    wvb;
    wva;
    wvc;
    wi2;
    wn;
    #;
    wva;
    wvb;
    wi2;
    wn;
    #;
    @0;
    wvc;
    wn;
    #;
    wva;
    wvc;
    wo;
    #;
    wa;
    @2;
    wva;
    wvc;
    ud2lem0c;
    @2;
    @3;
    lea;
    bltr;
    #;
    @1;
    wvb;
    wn;
    #;
    wva;
    wvb;
    wo;
    #;
    wa;
    @5;
    wva;
    wvb;
    ud2lem0c;
    @5;
    @6;
    lea;
    bltr;
    #;
    @0;
    wvc;
    @1;
    wvb;
    @4;
    @7;
    ax-oal4;
    @0;
    id;
    @1;
    id;
    oa4v3v;
    oal42;
    oa23;
  };

  return $|- ( ( a ->2 b ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =< ( a ->2 c )$;
}
