include "wo.mm"
include "wa.mm"
include "dp35lemd.mm"
include "dp35lemc.mm"
include "dp35lemb.mm"
include "tr.mm"
include "lbtr.mm"

theorem dp35lembb
  let wvp: term p
  let wva0: term a0
  let wva1: term a1
  let wva2: term a2
  let wvb0: term b0
  let wvb1: term b1
  let wvb2: term b2
  let wvc0: term c0
  let wvc1: term c1
  let wvc2: term c2
  let wvp0: term p0
  assume dp35lem.1: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume dp35lem.2: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume dp35lem.3: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume dp35lem.4: |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )
  assume dp35lem.5: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )


  assert |- ( b0 ^ ( a0 v p0 ) ) =< ( b0 ^ ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) ) )

  proof
    wvb0
    wva0
    wvp0
    wo
    wa
    wvb0
    wva0
    wvb0
    wa
    wvb1
    wo
    wvc2
    wvc0
    wvc1
    wo
    #
    wa
    #
    wo
    wa
    #
    wvb0
    wvb1
    wva0
    wva1
    wo
    @0
    wa
    wo
    wa
    #
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
    dp35lem.1
    dp35lem.2
    dp35lem.3
    dp35lem.4
    dp35lem.5
    dp35lemd
    @2
    wvb0
    wvb1
    @1
    wo
    wa
    @3
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
    dp35lem.1
    dp35lem.2
    dp35lem.3
    dp35lem.4
    dp35lem.5
    dp35lemc
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
    dp35lem.1
    dp35lem.2
    dp35lem.3
    dp35lem.4
    dp35lem.5
    dp35lemb
    tr
    lbtr
end
