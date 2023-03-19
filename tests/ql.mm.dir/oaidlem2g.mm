include "wa.mm"
include "wo.mm"
include "anidm.mm"
include "ax-r1.mm"
include "ran.mm"
include "anass.mm"
include "ax-r2.mm"
include "leor.mm"
include "lelan.mm"
include "bltr.mm"
include "df-le2.mm"
include "wn.mm"
include "wt.mm"
include "ax-a3.mm"
include "ax-a2.mm"
include "oran3.mm"
include "ax-r5.mm"
include "wi1.mm"
include "df-i1.mm"
include "lor.mm"
include "3tr2.mm"
include "lem3.1.mm"
include "bile.mm"
include "lear.mm"
include "letr.mm"

theorem oaidlem2g
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume oaidlem2g.1: |- ( ( c v ( a ^ b ) ) ' v ( a ->1 b ) ) = 1


  assert |- ( a ^ ( c v ( a ^ b ) ) ) =< b

  proof
    wva
    wvc
    wva
    wvb
    wa
    #
    wo
    #
    wa
    #
    @0
    wvb
    @2
    @0
    @0
    @2
    @0
    @2
    @0
    @2
    @0
    wva
    @0
    wa
    #
    @2
    @0
    wva
    wva
    wa
    #
    wvb
    wa
    @3
    wva
    @4
    wvb
    @4
    wva
    wva
    anidm
    ax-r1
    ran
    wva
    wva
    wvb
    anass
    ax-r2
    @0
    @1
    wva
    @0
    wvc
    leor
    lelan
    bltr
    df-le2
    @1
    wn
    #
    wva
    wn
    #
    wo
    #
    @0
    wo
    @5
    @6
    @0
    wo
    #
    wo
    #
    @2
    wn
    #
    @0
    wo
    wt
    @5
    @6
    @0
    ax-a3
    @7
    @10
    @0
    @7
    @6
    @5
    wo
    @10
    @5
    @6
    ax-a2
    wva
    @1
    oran3
    ax-r2
    ax-r5
    @9
    @5
    wva
    wvb
    wi1
    #
    wo
    #
    wt
    @12
    @9
    @11
    @8
    @5
    wva
    wvb
    df-i1
    lor
    ax-r1
    oaidlem2g.1
    ax-r2
    3tr2
    lem3.1
    ax-r1
    bile
    wva
    wvb
    lear
    letr
end
