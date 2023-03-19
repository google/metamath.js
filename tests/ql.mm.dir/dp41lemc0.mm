include "wo.mm"
include "wa.mm"
include "ax-a2.mm"
include "ror.mm"
include "or32.mm"
include "tr.mm"
include "lan.mm"
include "ancom.mm"
include "leor.mm"
include "ler.mm"
include "mldual2i.mm"
include "leo.mm"
include "3tr.mm"
include "orass.mm"
include "orcom.mm"

theorem dp41lemc0
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


  assert |- ( ( ( a0 v b0 ) v b1 ) ^ ( ( a0 v a1 ) v b1 ) ) = ( ( a0 v b1 ) v ( ( a0 v b0 ) ^ ( a1 v b1 ) ) )

  proof
    wva0
    wvb0
    wo
    #
    wvb1
    wo
    #
    wva0
    wva1
    wo
    #
    wvb1
    wo
    #
    wa
    #
    @0
    wva1
    wvb1
    wo
    #
    wa
    #
    wva0
    wo
    #
    wvb1
    wo
    #
    @6
    wva0
    wvb1
    wo
    #
    wo
    @9
    @6
    wo
    @4
    @5
    wva0
    wo
    #
    @1
    wa
    #
    @10
    @0
    wa
    #
    wvb1
    wo
    @8
    @4
    @1
    @10
    wa
    @11
    @3
    @10
    @1
    @3
    wva1
    wva0
    wo
    #
    wvb1
    wo
    @10
    @2
    @13
    wvb1
    wva0
    wva1
    ax-a2
    ror
    wva1
    wva0
    wvb1
    or32
    tr
    lan
    @1
    @10
    ancom
    tr
    wvb1
    @0
    @10
    wvb1
    @5
    wva0
    wvb1
    wva1
    leor
    ler
    mldual2i
    @12
    @7
    wvb1
    @12
    @0
    @10
    wa
    @7
    @10
    @0
    ancom
    wva0
    @5
    @0
    wva0
    wvb0
    leo
    mldual2i
    tr
    ror
    3tr
    @6
    wva0
    wvb1
    orass
    @6
    @9
    orcom
    3tr
end
