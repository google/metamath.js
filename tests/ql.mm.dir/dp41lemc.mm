include "wo.mm"
include "wa.mm"
include "anass.mm"
include "dp41lemc0.mm"
include "leo.mm"
include "dp41lema.mm"
include "lel2or.mm"
include "bltr.mm"
include "lelan.mm"

theorem dp41lemc
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


  assert |- ( ( c2 ^ ( ( a0 v b0 ) v b1 ) ) ^ ( ( a0 v a1 ) v b1 ) ) =< ( c2 ^ ( ( a0 v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) )

  proof
    wvc2
    wva0
    wvb0
    wo
    #
    wvb1
    wo
    #
    wa
    wva0
    wva1
    wo
    wvb1
    wo
    #
    wa
    wvc2
    @1
    @2
    wa
    #
    wa
    wvc2
    wva0
    wvb1
    wo
    #
    wvc2
    wvc0
    wvc1
    wo
    wa
    #
    wo
    #
    wa
    wvc2
    @1
    @2
    anass
    @3
    @6
    wvc2
    @3
    @4
    @0
    wva1
    wvb1
    wo
    wa
    #
    wo
    @6
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
    wvp2
    dp41lem.1
    dp41lem.2
    dp41lem.3
    dp41lem.4
    dp41lem.5
    dp41lem.6
    dp41lemc0
    @4
    @6
    @7
    @4
    @5
    leo
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
    wvp2
    dp41lem.1
    dp41lem.2
    dp41lem.3
    dp41lem.4
    dp41lem.5
    dp41lem.6
    dp41lema
    lel2or
    bltr
    lelan
    bltr
end
