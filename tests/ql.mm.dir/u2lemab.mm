include "wi2.mm";
include "wa.mm";
include "wn.mm";
include "wo.mm";
include "df-i2.mm";
include "ran.mm";
include "ancom.mm";
include "anabs.mm";
include "ax-r2.mm";

theorem u2lemab(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi2;
    #;
    wvb;
    wa;
    wvb;
    wva;
    wn;
    wvb;
    wn;
    wa;
    #;
    wo;
    #;
    wvb;
    wa;
    #;
    wvb;
    @0;
    @2;
    wvb;
    wva;
    wvb;
    df-i2;
    ran;
    @3;
    wvb;
    @2;
    wa;
    wvb;
    @2;
    wvb;
    ancom;
    wvb;
    @1;
    anabs;
    ax-r2;
    ax-r2;
  };

  return $|- ( ( a ->2 b ) ^ b ) = b$;
}
