include "wo.mm"
include "wa.mm"
include "dp32.mm"
include "lea.mm"
include "leror.mm"
include "letr.mm"

theorem dp23
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
  assume dp23.1: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume dp23.2: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume dp23.3: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume dp23.4: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )


  assert |- p =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) )

  proof
    wvp
    wva0
    wva1
    wvc2
    wvc0
    wvc1
    wo
    wa
    #
    wo
    #
    wa
    #
    wvb0
    wvb1
    @0
    wo
    wa
    #
    wo
    wva0
    @3
    wo
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
    dp23.1
    dp23.2
    dp23.3
    dp23.4
    dp32
    @2
    wva0
    @3
    wva0
    @1
    lea
    leror
    letr
end
