include "wa.mm"
include "wo.mm"
include "or32.mm"
include "orcom.mm"
include "leo.mm"
include "le2an.mm"
include "cm.mm"
include "lbtr.mm"
include "lerr.mm"
include "ler2an.mm"
include "df-le2.mm"
include "lor.mm"
include "3tr.mm"
include "lan.mm"

theorem dp53lemc
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
  assume dp53lem.1: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume dp53lem.2: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume dp53lem.3: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume dp53lem.4: |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )
  assume dp53lem.5: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )


  assert |- ( b0 ^ ( ( ( a0 ^ b0 ) v b1 ) v ( c2 ^ ( c0 v c1 ) ) ) ) = ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) )

  proof
    wva0
    wvb0
    wa
    #
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
    #
    wvb1
    @2
    wo
    #
    wvb0
    @3
    @0
    @2
    wo
    #
    wvb1
    wo
    wvb1
    @5
    wo
    @4
    @0
    wvb1
    @2
    or32
    @5
    wvb1
    orcom
    @5
    @2
    wvb1
    @0
    @2
    @0
    wvc2
    @1
    @0
    wva0
    wva1
    wo
    #
    wvb0
    wvb1
    wo
    #
    wa
    #
    wvc2
    wva0
    @6
    wvb0
    @7
    wva0
    wva1
    leo
    wvb0
    wvb1
    leo
    le2an
    wvc2
    @8
    dp53lem.3
    cm
    lbtr
    @0
    wvc1
    wvc0
    @0
    wva0
    wva2
    wo
    #
    wvb0
    wvb2
    wo
    #
    wa
    #
    wvc1
    wva0
    @9
    wvb0
    @10
    wva0
    wva2
    leo
    wvb0
    wvb2
    leo
    le2an
    wvc1
    @11
    dp53lem.2
    cm
    lbtr
    lerr
    ler2an
    df-le2
    lor
    3tr
    lan
end
