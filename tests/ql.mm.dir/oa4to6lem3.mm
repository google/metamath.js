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
include "lelan.mm"
include "lelor.mm"
include "letr.mm"
include "ud1lem0a.mm"
include "df-i1.mm"

theorem oa4to6lem3
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


  assert |- f =< ( e ->1 g )

  proof
    wvf
    wve
    wn
    #
    wve
    wva
    wvb
    wa
    wvc
    wvd
    wa
    wo
    #
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
    wve
    wvg
    wi1
    #
    wvf
    @0
    wve
    @2
    wa
    #
    wo
    #
    @5
    wvf
    @0
    wvf
    wo
    #
    @8
    wvf
    @0
    leor
    @9
    @0
    @2
    wo
    #
    @8
    @10
    @9
    @10
    @0
    wve
    wo
    #
    @9
    wa
    #
    @9
    @0
    wve
    wvf
    wve
    wve
    wve
    comid
    comcom3
    @0
    wvf
    oa4to6lem.3
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
    wve
    @0
    wo
    @11
    wve
    df-t
    wve
    @0
    ax-a2
    ax-r2
    ran
    @9
    an1
    3tr2
    ax-r2
    ax-r1
    @2
    @7
    @0
    @2
    wve
    wve
    wa
    #
    wvf
    wa
    #
    @7
    @14
    @2
    @13
    wve
    wvf
    wve
    anidm
    ran
    ax-r1
    wve
    wve
    wvf
    anass
    ax-r2
    lor
    ax-r2
    lbtr
    @7
    @4
    @0
    @2
    @3
    wve
    @2
    @1
    leor
    lelan
    lelor
    letr
    @6
    @5
    @6
    wve
    @3
    wi1
    @5
    wvg
    @3
    wve
    oa4to6lem.4
    ud1lem0a
    wve
    @3
    df-i1
    ax-r2
    ax-r1
    lbtr
end
