include "wo.mm"
include "wa.mm"
include "leor.mm"
include "dp53lemf.mm"
include "letr.mm"

theorem dp53lemg
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
  param wvp0: term p0
  assume dp53lem.1: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume dp53lem.2: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume dp53lem.3: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume dp53lem.4: |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )
  assume dp53lem.5: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )


  assert |- p =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) )

  proof
    wvp
    wva0
    wvp
    wo
    wva0
    wvb0
    wvb1
    wvc2
    wvc0
    wvc1
    wo
    wa
    wo
    wa
    wo
    wvp
    wva0
    leor
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
    wvp0
    dp53lem.1
    dp53lem.2
    dp53lem.3
    dp53lem.4
    dp53lem.5
    dp53lemf
    letr
end
