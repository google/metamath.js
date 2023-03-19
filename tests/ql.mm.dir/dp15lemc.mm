include "wo.mm"
include "wa.mm"
include "dp15lemb.mm"
include "ror.mm"
include "lan.mm"
include "lor.mm"
include "2an.mm"
include "ran.mm"
include "2or.mm"
include "le3tr2.mm"

theorem dp15lemc
  param wvd: term d
  param wve: term e
  param wva0: term a0
  param wva1: term a1
  param wva2: term a2
  param wvb0: term b0
  param wvb1: term b1
  param wvb2: term b2
  param wvp0: term p0
  assume dp15lema.1: |- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) )
  assume dp15lema.2: |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )
  assume dp15lema.3: |- e = ( b0 ^ ( a0 v p0 ) )


  assert |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) ) =< ( ( ( a0 v ( a2 v ( a0 ^ ( a1 v b1 ) ) ) ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) ) v ( ( a1 v ( a2 v ( a0 ^ ( a1 v b1 ) ) ) ) ^ ( b1 v b2 ) ) )

  proof
    wva0
    wva1
    wo
    #
    wve
    wvb1
    wo
    #
    wa
    wva0
    wvd
    wo
    #
    wve
    wvb2
    wo
    #
    wa
    #
    wva1
    wvd
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
    wva0
    wvp0
    wo
    wa
    #
    wvb1
    wo
    #
    wa
    wva0
    wva2
    wva0
    wva1
    wvb1
    wo
    wa
    wo
    #
    wo
    #
    @8
    wvb2
    wo
    #
    wa
    #
    wva1
    @10
    wo
    #
    @6
    wa
    #
    wo
    wvd
    wve
    wva0
    wva1
    wva2
    wvb0
    wvb1
    wvb2
    wvp0
    dp15lema.1
    dp15lema.2
    dp15lema.3
    dp15lemb
    @1
    @9
    @0
    wve
    @8
    wvb1
    dp15lema.3
    ror
    lan
    @4
    @13
    @7
    @15
    @2
    @11
    @3
    @12
    wvd
    @10
    wva0
    dp15lema.1
    lor
    wve
    @8
    wvb2
    dp15lema.3
    ror
    2an
    @5
    @14
    @6
    wvd
    @10
    wva1
    dp15lema.1
    lor
    ran
    2or
    le3tr2
end
