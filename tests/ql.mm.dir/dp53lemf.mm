include "wo.mm"
include "wa.mm"
include "leo.mm"
include "anass.mm"
include "tr.mm"
include "lan.mm"
include "cm.mm"
include "leao4.mm"
include "bltr.mm"
include "lea.mm"
include "orcom.mm"
include "lbtr.mm"
include "ler2an.mm"
include "mldual2i.mm"
include "ancom.mm"
include "ror.mm"
include "lelor.mm"
include "letr.mm"
include "dp53leme.mm"
include "df-le2.mm"
include "lel2or.mm"

theorem dp53lemf
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


  assert |- ( a0 v p ) =< ( a0 v ( b0 ^ ( b1 v ( c2 ^ ( c0 v c1 ) ) ) ) )

  proof
    wva0
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
    #
    wo
    #
    wvp
    wva0
    @0
    leo
    #
    wvp
    wvb0
    wva0
    wvp0
    wo
    #
    wa
    #
    @1
    wo
    #
    @1
    wvp
    @4
    wva0
    wo
    #
    @5
    wvp
    @3
    wvb0
    wva0
    wo
    #
    wa
    #
    @6
    wvp
    wva0
    wvb0
    wo
    #
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
    wa
    #
    @8
    wvp
    @9
    @10
    wa
    @11
    wa
    @13
    dp53lem.5
    @9
    @10
    @11
    anass
    tr
    @13
    @3
    @7
    @13
    @9
    wvp0
    wa
    #
    @3
    @14
    @13
    wvp0
    @12
    @9
    dp53lem.4
    lan
    cm
    wvp0
    @9
    wva0
    leao4
    bltr
    @13
    @9
    @7
    @9
    @12
    lea
    wva0
    wvb0
    orcom
    lbtr
    ler2an
    bltr
    @8
    @3
    wvb0
    wa
    #
    wva0
    wo
    @6
    wva0
    wvb0
    @3
    wva0
    wvp0
    leo
    mldual2i
    @15
    @4
    wva0
    @3
    wvb0
    ancom
    ror
    tr
    lbtr
    wva0
    @1
    @4
    @2
    lelor
    letr
    @4
    @1
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
    dp53leme
    df-le2
    lbtr
    lel2or
end
