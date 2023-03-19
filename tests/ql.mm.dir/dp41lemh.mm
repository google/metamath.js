include "wo.mm"
include "wa.mm"
include "lea.mm"
include "leo.mm"
include "leran.mm"
include "cm.mm"
include "bltr.mm"
include "letr.mm"
include "ler2an.mm"
include "lelor.mm"
include "lelan.mm"
include "lear.mm"
include "leao3.mm"
include "le2or.mm"

theorem dp41lemh
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


  assert |- ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( a0 ^ ( a1 v b1 ) ) ) ) v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( b1 ^ ( a0 v b0 ) ) ) ) ) =< ( ( ( b1 v b2 ) ^ ( ( a1 v a2 ) v ( a0 ^ ( a2 v b2 ) ) ) ) v ( ( a0 v a2 ) ^ ( ( b0 v b2 ) v ( b1 ^ ( a2 v b2 ) ) ) ) )

  proof
    wvb1
    wvb2
    wo
    #
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
    wa
    @0
    @1
    wva0
    wva2
    wvb2
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
    wvb1
    wva0
    wvb0
    wo
    #
    wa
    #
    wo
    #
    wa
    @8
    @9
    wvb1
    @5
    wa
    #
    wo
    #
    wa
    @4
    @7
    @0
    @3
    @6
    @1
    @3
    wva0
    @5
    wva0
    @2
    lea
    @3
    @10
    @2
    wa
    #
    @5
    wva0
    @10
    @2
    wva0
    wvb0
    leo
    leran
    @15
    wvp2
    @5
    wvp2
    @15
    dp41lem.5
    cm
    dp41lem.6
    bltr
    #
    letr
    ler2an
    lelor
    lelan
    @12
    @14
    @8
    @11
    @13
    @9
    @11
    wvb1
    @5
    wvb1
    @10
    lea
    @11
    @15
    @5
    @11
    @10
    @2
    wvb1
    @10
    lear
    wvb1
    @10
    wva1
    leao3
    ler2an
    @16
    letr
    ler2an
    lelor
    lelan
    le2or
end
