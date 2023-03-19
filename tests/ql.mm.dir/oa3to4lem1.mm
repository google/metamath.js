include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "leor.mm"
include "comid.mm"
include "comcom3.mm"
include "lecom.mm"
include "fh3.mm"
include "wt.mm"
include "ancom.mm"
include "df-t.mm"
include "ax-a2.mm"
include "ax-r2.mm"
include "ran.mm"
include "an1.mm"
include "3tr2.mm"
include "ax-r1.mm"
include "anidm.mm"
include "anass.mm"
include "lor.mm"
include "lbtr.mm"
include "leo.mm"
include "lelan.mm"
include "lelor.mm"
include "letr.mm"
include "ud1lem0a.mm"
include "df-i1.mm"

theorem oa3to4lem1
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wvg: term g
  assume oa3to4lem.1: |- a ' =< b
  assume oa3to4lem.2: |- c ' =< d
  assume oa3to4lem.3: |- g = ( ( a ^ b ) v ( c ^ d ) )


  assert |- b =< ( a ->1 g )

  proof
    wvb
    wva
    wn
    #
    wva
    wva
    wvb
    wa
    #
    wvc
    wvd
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wva
    wvg
    wi1
    #
    wvb
    @0
    wva
    @1
    wa
    #
    wo
    #
    @5
    wvb
    @0
    wvb
    wo
    #
    @8
    wvb
    @0
    leor
    @9
    @0
    @1
    wo
    #
    @8
    @10
    @9
    @10
    @0
    wva
    wo
    #
    @9
    wa
    #
    @9
    @0
    wva
    wvb
    wva
    wva
    wva
    comid
    comcom3
    @0
    wvb
    oa3to4lem.1
    lecom
    fh3
    wt
    @9
    wa
    @9
    wt
    wa
    @12
    @9
    wt
    @9
    ancom
    wt
    @11
    @9
    wt
    wva
    @0
    wo
    @11
    wva
    df-t
    wva
    @0
    ax-a2
    ax-r2
    ran
    @9
    an1
    3tr2
    ax-r2
    ax-r1
    @1
    @7
    @0
    @1
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @7
    @14
    @1
    @13
    wva
    wvb
    wva
    anidm
    ran
    ax-r1
    wva
    wva
    wvb
    anass
    ax-r2
    lor
    ax-r2
    lbtr
    @7
    @4
    @0
    @1
    @3
    wva
    @1
    @2
    leo
    lelan
    lelor
    letr
    @6
    @5
    @6
    wva
    @3
    wi1
    @5
    wvg
    @3
    wva
    oa3to4lem.3
    ud1lem0a
    wva
    @3
    df-i1
    ax-r2
    ax-r1
    lbtr
end
