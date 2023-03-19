include "wo.mm"
include "wa.mm"
include "leo.mm"
include "lor.mm"
include "lan.mm"
include "lear.mm"
include "lea.mm"
include "lelor.mm"
include "ax-a3.mm"
include "cm.mm"
include "lbtr.mm"
include "letr.mm"
include "bltr.mm"
include "ler2an.mm"
include "leor.mm"
include "mldual2i.mm"
include "ancom.mm"
include "ror.mm"
include "tr.mm"
include "dp15.mm"
include "orcom.mm"
include "leid.mm"
include "lel2or.mm"

theorem dp53lema
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


  assert |- ( b1 v ( b0 ^ ( a0 v p0 ) ) ) =< ( b1 v ( ( a0 v a1 ) ^ ( c0 v c1 ) ) )

  proof
    wvb1
    wvb1
    wva0
    wva1
    wo
    #
    wvc0
    wvc1
    wo
    #
    wa
    #
    wo
    #
    wvb0
    wva0
    wvp0
    wo
    #
    wa
    #
    wvb1
    @2
    leo
    #
    @5
    @0
    @5
    wvb1
    wo
    #
    wa
    #
    @3
    wo
    #
    @3
    @5
    @8
    wvb1
    wo
    #
    @9
    @5
    @7
    @0
    wvb1
    wo
    #
    wa
    #
    @10
    @5
    @7
    @11
    @5
    wvb1
    leo
    @5
    wvb0
    wva0
    wva1
    wvb1
    wo
    #
    wva2
    wvb2
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    @11
    @4
    @16
    wvb0
    wvp0
    @15
    wva0
    dp53lem.4
    lor
    lan
    @17
    @16
    @11
    wvb0
    @16
    lear
    @16
    wva0
    @13
    wo
    #
    @11
    @15
    @13
    wva0
    @13
    @14
    lea
    lelor
    @11
    @18
    wva0
    wva1
    wvb1
    ax-a3
    cm
    lbtr
    letr
    bltr
    ler2an
    @12
    @7
    @0
    wa
    #
    wvb1
    wo
    @10
    wvb1
    @0
    @7
    wvb1
    @5
    leor
    mldual2i
    @19
    @8
    wvb1
    @7
    @0
    ancom
    ror
    tr
    lbtr
    wvb1
    @3
    @8
    @6
    lelor
    letr
    @8
    @3
    @3
    @8
    @2
    wvb1
    wo
    #
    @3
    @8
    @2
    wvb1
    @0
    wa
    #
    wo
    #
    @20
    @8
    @0
    @1
    @21
    wo
    #
    wa
    @22
    @8
    @0
    @23
    @0
    @7
    lea
    wva0
    wva1
    wva2
    wvb0
    wvb1
    wvb2
    wvc0
    wvc1
    wvp0
    dp53lem.1
    dp53lem.2
    dp53lem.4
    dp15
    ler2an
    @21
    @1
    @0
    wvb1
    @0
    lear
    mldual2i
    lbtr
    @21
    wvb1
    @2
    wvb1
    @0
    lea
    lelor
    letr
    @2
    wvb1
    orcom
    lbtr
    @3
    leid
    lel2or
    letr
    lel2or
end
