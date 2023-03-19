include "wo.mm"
include "wa.mm"
include "lea.mm"
include "leror.mm"
include "lelan.mm"
include "leao1.mm"
include "mldual2i.mm"
include "ancom.mm"
include "ror.mm"
include "3tr2.mm"
include "bile.mm"
include "le2or.mm"
include "or12.mm"
include "lbtr.mm"

theorem dp15lemf
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


  assert |- ( ( ( a0 v a2 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) ) v ( ( ( a1 v a2 ) v ( b1 ^ ( a0 v a1 ) ) ) ^ ( b1 v b2 ) ) ) =< ( ( ( a1 v a2 ) ^ ( b1 v b2 ) ) v ( ( ( a0 v a2 ) ^ ( b0 v b2 ) ) v ( b1 ^ ( a0 v a1 ) ) ) )

  proof
    wva0
    wva2
    wo
    #
    wvb0
    wva0
    wvp0
    wo
    #
    wa
    #
    wvb2
    wo
    #
    wa
    #
    wva1
    wva2
    wo
    #
    wvb1
    wva0
    wva1
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
    #
    wo
    @0
    wvb0
    wvb2
    wo
    #
    wa
    #
    @5
    @9
    wa
    #
    @7
    wo
    #
    wo
    @13
    @12
    @7
    wo
    wo
    @4
    @12
    @10
    @14
    @3
    @11
    @0
    @2
    wvb0
    wvb2
    wvb0
    @1
    lea
    leror
    lelan
    @10
    @14
    @9
    @8
    wa
    @9
    @5
    wa
    #
    @7
    wo
    @10
    @14
    @7
    @5
    @9
    wvb1
    @6
    wvb2
    leao1
    mldual2i
    @9
    @8
    ancom
    @15
    @13
    @7
    @9
    @5
    ancom
    ror
    3tr2
    bile
    le2or
    @12
    @13
    @7
    or12
    lbtr
end
