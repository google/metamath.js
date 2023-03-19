include "wo.mm"
include "wa.mm"
include "or32.mm"
include "ml3.mm"
include "orcom.mm"
include "lan.mm"
include "lor.mm"
include "tr.mm"
include "ror.mm"
include "3tr.mm"
include "2or.mm"

theorem dp41lemg
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
  let wvp2: term p2
  assume dp41lem.1: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume dp41lem.2: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume dp41lem.3: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume dp41lem.4: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )
  assume dp41lem.5: |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) )
  assume dp41lem.6: |- p2 =< ( a2 v b2 )


  assert |- ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( b1 ^ ( a0 v a1 ) ) ) ) v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( a0 ^ ( b0 v b1 ) ) ) ) ) = ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( a0 ^ ( a1 v b1 ) ) ) ) v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( b1 ^ ( a0 v b0 ) ) ) ) )

  proof
    wvb1
    wvb2
    wo
    #
    wva1
    wva2
    wo
    #
    wvb1
    wva0
    wva1
    wo
    wa
    #
    wo
    #
    wa
    @0
    @1
    wva0
    wva1
    wvb1
    wo
    #
    wa
    #
    wo
    #
    wa
    wva0
    wva2
    wo
    #
    wvb0
    wvb2
    wo
    #
    wva0
    wvb0
    wvb1
    wo
    #
    wa
    #
    wo
    #
    wa
    @7
    @8
    wvb1
    wva0
    wvb0
    wo
    wa
    #
    wo
    #
    wa
    @3
    @6
    @0
    @3
    wva1
    @2
    wo
    #
    wva2
    wo
    wva1
    @5
    wo
    #
    wva2
    wo
    @6
    wva1
    wva2
    @2
    or32
    @14
    @15
    wva2
    @14
    wva1
    wva0
    wvb1
    wva1
    wo
    #
    wa
    #
    wo
    @15
    wva1
    wvb1
    wva0
    ml3
    @17
    @5
    wva1
    @16
    @4
    wva0
    wvb1
    wva1
    orcom
    lan
    lor
    tr
    ror
    wva1
    @5
    wva2
    or32
    3tr
    lan
    @11
    @13
    @7
    @11
    wvb0
    @10
    wo
    #
    wvb2
    wo
    wvb0
    @12
    wo
    #
    wvb2
    wo
    @13
    wvb0
    wvb2
    @10
    or32
    @18
    @19
    wvb2
    @18
    wvb0
    wva0
    wvb1
    wvb0
    wo
    #
    wa
    #
    wo
    @19
    @10
    @21
    wvb0
    @9
    @20
    wva0
    wvb0
    wvb1
    orcom
    lan
    lor
    wvb0
    wva0
    wvb1
    ml3
    tr
    ror
    wvb0
    @12
    wvb2
    or32
    3tr
    lan
    2or
end
