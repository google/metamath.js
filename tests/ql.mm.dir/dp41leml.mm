include "wo.mm"
include "wa.mm"
include "or4.mm"
include "orcom.mm"
include "ancom.mm"
include "leor.mm"
include "lelan.mm"
include "bltr.mm"
include "leran.mm"
include "le2or.mm"
include "2or.mm"
include "cm.mm"
include "tr.mm"
include "lbtr.mm"
include "df-le2.mm"
include "3tr.mm"

theorem dp41leml
  param wvp: term p
  param wva0: term a0
  param wva1: term a1
  param wva2: term a2
  param wvb0: term b0
  param wvb1: term b1
  param wvb2: term b2
  param wvc0: term c0
  param wvc1: term c1
  param wvc2: term c2
  param wvp2: term p2
  assume dp41lem.1: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume dp41lem.2: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume dp41lem.3: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume dp41lem.4: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )
  assume dp41lem.5: |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) )
  assume dp41lem.6: |- p2 =< ( a2 v b2 )


  assert |- ( ( c0 v ( b2 ^ ( a0 v a2 ) ) ) v ( c1 v ( a2 ^ ( b1 v b2 ) ) ) ) = ( c0 v c1 )

  proof
    wvc0
    wvb2
    wva0
    wva2
    wo
    #
    wa
    #
    wo
    wvc1
    wva2
    wvb1
    wvb2
    wo
    #
    wa
    #
    wo
    wo
    wvc0
    wvc1
    wo
    #
    @1
    @3
    wo
    #
    wo
    @5
    @4
    wo
    @4
    wvc0
    @1
    wvc1
    @3
    or4
    @4
    @5
    orcom
    @5
    @4
    @5
    @0
    wvb0
    wvb2
    wo
    #
    wa
    #
    wva1
    wva2
    wo
    #
    @2
    wa
    #
    wo
    #
    @4
    @1
    @7
    @3
    @9
    @1
    @0
    wvb2
    wa
    @7
    wvb2
    @0
    ancom
    wvb2
    @6
    @0
    wvb2
    wvb0
    leor
    lelan
    bltr
    wva2
    @8
    @2
    wva2
    wva1
    leor
    leran
    le2or
    @10
    wvc1
    wvc0
    wo
    #
    @4
    @11
    @10
    wvc1
    @7
    wvc0
    @9
    dp41lem.2
    dp41lem.1
    2or
    cm
    wvc1
    wvc0
    orcom
    tr
    lbtr
    df-le2
    3tr
end
