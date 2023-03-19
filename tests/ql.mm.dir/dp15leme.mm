include "wo.mm"
include "wa.mm"
include "ax-a2.mm"
include "lan.mm"
include "2or.mm"
include "orass.mm"
include "tr.mm"
include "ml3le.mm"
include "lelor.mm"
include "bltr.mm"
include "cm.mm"
include "ror.mm"
include "lbtr.mm"
include "leran.mm"

theorem dp15leme
  let wvd: term d
  let wve: term e
  let wva0: term a0
  let wva1: term a1
  let wva2: term a2
  let wvb0: term b0
  let wvb1: term b1
  let wvb2: term b2
  let wvp0: term p0
  assume dp15lema.1: |- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) )
  assume dp15lema.2: |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )
  assume dp15lema.3: |- e = ( b0 ^ ( a0 v p0 ) )


  assert |- ( ( ( a0 v a2 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) ) v ( ( ( a1 v a2 ) v ( a0 ^ ( a1 v b1 ) ) ) ^ ( b1 v b2 ) ) ) =< ( ( ( a0 v a2 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) ) v ( ( ( a1 v a2 ) v ( b1 ^ ( a0 v a1 ) ) ) ^ ( b1 v b2 ) ) )

  proof
    wva1
    wva2
    wo
    #
    wva0
    wva1
    wvb1
    wo
    #
    wa
    #
    wo
    #
    wvb1
    wvb2
    wo
    #
    wa
    @0
    wvb1
    wva0
    wva1
    wo
    wa
    #
    wo
    #
    @4
    wa
    wva0
    wva2
    wo
    wvb0
    wva0
    wvp0
    wo
    wa
    wvb2
    wo
    wa
    @3
    @6
    @4
    @3
    wva2
    wva1
    @5
    wo
    #
    wo
    #
    @6
    @3
    wva2
    wva1
    wva0
    wvb1
    wva1
    wo
    #
    wa
    #
    wo
    #
    wo
    #
    @8
    @3
    wva2
    wva1
    wo
    #
    @10
    wo
    @12
    @0
    @13
    @2
    @10
    wva1
    wva2
    ax-a2
    @1
    @9
    wva0
    wva1
    wvb1
    ax-a2
    lan
    2or
    wva2
    wva1
    @10
    orass
    tr
    @11
    @7
    wva2
    wva1
    wva0
    wvb1
    ml3le
    lelor
    bltr
    @8
    @13
    @5
    wo
    #
    @6
    @14
    @8
    wva2
    wva1
    @5
    orass
    cm
    @13
    @0
    @5
    wva2
    wva1
    ax-a2
    ror
    tr
    lbtr
    leran
    lelor
end
