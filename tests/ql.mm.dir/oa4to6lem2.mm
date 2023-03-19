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
include "or32.mm"
include "lelan.mm"
include "lelor.mm"
include "letr.mm"
include "ud1lem0a.mm"
include "df-i1.mm"

theorem oa4to6lem2
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  let wvf: term f
  let wvg: term g
  assume oa4to6lem.1: |- a ' =< b
  assume oa4to6lem.2: |- c ' =< d
  assume oa4to6lem.3: |- e ' =< f
  assume oa4to6lem.4: |- g = ( ( ( a ^ b ) v ( c ^ d ) ) v ( e ^ f ) )


  assert |- d =< ( c ->1 g )

  proof
    wvd
    wvc
    wn
    #
    wvc
    wva
    wvb
    wa
    #
    wvc
    wvd
    wa
    #
    wo
    wve
    wvf
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    wvc
    wvg
    wi1
    #
    wvd
    @0
    wvc
    @2
    wa
    #
    wo
    #
    @6
    wvd
    @0
    wvd
    wo
    #
    @9
    wvd
    @0
    leor
    @10
    @0
    @2
    wo
    #
    @9
    @11
    @10
    @11
    @0
    wvc
    wo
    #
    @10
    wa
    #
    @10
    @0
    wvc
    wvd
    wvc
    wvc
    wvc
    comid
    comcom3
    @0
    wvd
    oa4to6lem.2
    lecom
    fh3
    wt
    @10
    wa
    @10
    wt
    wa
    @13
    @10
    wt
    @10
    ancom
    wt
    @12
    @10
    wt
    wvc
    @0
    wo
    @12
    wvc
    df-t
    wvc
    @0
    ax-a2
    ax-r2
    ran
    @10
    an1
    3tr2
    ax-r2
    ax-r1
    @2
    @8
    @0
    @2
    wvc
    wvc
    wa
    #
    wvd
    wa
    #
    @8
    @15
    @2
    @14
    wvc
    wvd
    wvc
    anidm
    ran
    ax-r1
    wvc
    wvc
    wvd
    anass
    ax-r2
    lor
    ax-r2
    lbtr
    @8
    @5
    @0
    @2
    @4
    wvc
    @2
    @1
    @3
    wo
    #
    @2
    wo
    @4
    @2
    @16
    leor
    @1
    @3
    @2
    or32
    lbtr
    lelan
    lelor
    letr
    @7
    @6
    @7
    wvc
    @4
    wi1
    @6
    wvg
    @4
    wvc
    oa4to6lem.4
    ud1lem0a
    wvc
    @4
    df-i1
    ax-r2
    ax-r1
    lbtr
end
