include "wo.mm"
include "wa.mm"
include "dp53.mm"
include "lear.mm"
include "lelor.mm"
include "letr.mm"
include "orass.mm"
include "cm.mm"
include "lbtr.mm"

theorem dp34
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
  assume dp34.1: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume dp34.2: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume dp34.3: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume dp34.4: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )


  assert |- p =< ( ( a0 v b1 ) v ( c2 ^ ( c0 v c1 ) ) )

  proof
    wvp
    wva0
    wvb1
    wvc2
    wvc0
    wvc1
    wo
    wa
    #
    wo
    #
    wo
    #
    wva0
    wvb1
    wo
    @0
    wo
    #
    wvp
    wva0
    wvb0
    @1
    wa
    #
    wo
    @2
    wvp
    wva0
    wva1
    wva2
    wvb0
    wvb1
    wvb2
    wvc0
    wvc1
    wvc2
    dp34.1
    dp34.2
    dp34.3
    dp34.4
    dp53
    @4
    @1
    wva0
    wvb0
    @1
    lear
    lelor
    letr
    @3
    @2
    wva0
    wvb1
    @0
    orass
    cm
    lbtr
end
