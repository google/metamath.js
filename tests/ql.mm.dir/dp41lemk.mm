include "wo.mm"
include "wa.mm"
include "leao3.mm"
include "mldual2i.mm"
include "ancom.mm"
include "tr.mm"
include "ror.mm"
include "cm.mm"
include "2or.mm"

theorem dp41lemk
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


  assert |- ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( b2 ^ ( a0 v a2 ) ) ) ) v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( a2 ^ ( b1 v b2 ) ) ) ) ) = ( ( c0 v ( b2 ^ ( a0 v a2 ) ) ) v ( c1 v ( a2 ^ ( b1 v b2 ) ) ) )

  proof
    wvb1
    wvb2
    wo
    #
    wva1
    wva2
    wo
    #
    wvb2
    wva0
    wva2
    wo
    #
    wa
    #
    wo
    wa
    #
    wvc0
    @3
    wo
    #
    @2
    wvb0
    wvb2
    wo
    #
    wva2
    @0
    wa
    #
    wo
    wa
    #
    wvc1
    @7
    wo
    #
    @4
    @0
    @1
    wa
    #
    @3
    wo
    #
    @5
    @3
    @1
    @0
    wvb2
    @2
    wvb1
    leao3
    mldual2i
    @5
    @11
    wvc0
    @10
    @3
    wvc0
    @1
    @0
    wa
    @10
    dp41lem.1
    @1
    @0
    ancom
    tr
    ror
    cm
    tr
    @8
    @2
    @6
    wa
    #
    @7
    wo
    #
    @9
    @7
    @6
    @2
    wva2
    @0
    wva0
    leao3
    mldual2i
    @9
    @13
    wvc1
    @12
    @7
    dp41lem.2
    ror
    cm
    tr
    2or
end
