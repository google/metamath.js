include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "anor3.mm"
include "lan.mm"
include "ax-r1.mm"
include "anass.mm"
include "ax-r2.mm"
include "ancom.mm"
include "omlan.mm"
include "lear.mm"
include "bltr.mm"
include "leran.mm"
include "leor.mm"
include "letr.mm"
include "df-i2.mm"
include "lor.mm"
include "ran.mm"
include "le3tr1.mm"

theorem 3vth1
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a ->2 b ) ^ ( b v c ) ' ) =< ( a ->2 c )

  proof
    wvb
    wvb
    wn
    #
    wva
    wn
    #
    wa
    #
    wo
    #
    wvb
    wvc
    wo
    wn
    #
    wa
    #
    wvc
    @1
    wvc
    wn
    #
    wa
    #
    wo
    #
    wva
    wvb
    wi2
    #
    @4
    wa
    wva
    wvc
    wi2
    @5
    @7
    @8
    @5
    @3
    @0
    wa
    #
    @6
    wa
    #
    @7
    @5
    @3
    @0
    @6
    wa
    #
    wa
    #
    @11
    @13
    @5
    @12
    @4
    @3
    wvb
    wvc
    anor3
    lan
    ax-r1
    @11
    @13
    @3
    @0
    @6
    anass
    ax-r1
    ax-r2
    @10
    @1
    @6
    @10
    @2
    @1
    @10
    @0
    @3
    wa
    @2
    @3
    @0
    ancom
    wvb
    @1
    omlan
    ax-r2
    @0
    @1
    lear
    bltr
    leran
    bltr
    @7
    wvc
    leor
    letr
    @9
    @3
    @4
    @9
    wvb
    @1
    @0
    wa
    #
    wo
    @3
    wva
    wvb
    df-i2
    @14
    @2
    wvb
    @1
    @0
    ancom
    lor
    ax-r2
    ran
    wva
    wvc
    df-i2
    le3tr1
end
