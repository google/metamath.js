include "wo.mm"
include "wa.mm"
include "or12.mm"
include "orabs.mm"
include "lor.mm"
include "orcom.mm"
include "3tr.mm"
include "ran.mm"
include "orass.mm"
include "cm.mm"
include "2or.mm"

theorem dp15lemd
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


  assert |- ( ( ( a0 v ( a2 v ( a0 ^ ( a1 v b1 ) ) ) ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) ) v ( ( a1 v ( a2 v ( a0 ^ ( a1 v b1 ) ) ) ) ^ ( b1 v b2 ) ) ) = ( ( ( a0 v a2 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b2 ) ) v ( ( ( a1 v a2 ) v ( a0 ^ ( a1 v b1 ) ) ) ^ ( b1 v b2 ) ) )

  proof
    wva0
    wva2
    wva0
    wva1
    wvb1
    wo
    #
    wa
    #
    wo
    #
    wo
    #
    wvb0
    wva0
    wvp0
    wo
    wa
    wvb2
    wo
    #
    wa
    wva0
    wva2
    wo
    #
    @4
    wa
    wva1
    @2
    wo
    #
    wvb1
    wvb2
    wo
    #
    wa
    #
    wva1
    wva2
    wo
    @1
    wo
    #
    @7
    wa
    #
    @3
    @5
    @4
    @3
    wva2
    wva0
    @1
    wo
    #
    wo
    wva2
    wva0
    wo
    @5
    wva0
    wva2
    @1
    or12
    @11
    wva0
    wva2
    wva0
    @0
    orabs
    lor
    wva2
    wva0
    orcom
    3tr
    ran
    @10
    @8
    @9
    @6
    @7
    wva1
    wva2
    @1
    orass
    ran
    cm
    2or
end
