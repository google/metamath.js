include "wcel.mm"
include "cfcls.mm"
include "co.mm"
include "ccl.mm"
include "cfv.mm"
include "cv.mm"
include "wral.mm"
include "ctop.mm"
include "cuni.mm"
include "cfil.mm"
include "eqid.mm"
include "isfcls.mm"
include "simp3bi.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspcv.mm"
include "syl5.mm"
include "ssrdv.mm"

theorem fclssscls
  let cS: class S
  let cF: class F
  let cJ: class J
  let vn: setvar n
  let vo: setvar o
  let vs: setvar s
  let cA: class A
  let vx: setvar x
  let cX: class X
  let cU: class U


  assert |- ( S e. F -> ( J fClus F ) C_ ( ( cls ` J ) ` S ) )

  proof
    cS
    cF
    wcel
    #
    vx
    cJ
    cF
    cfcls
    co
    #
    cS
    cJ
    ccl
    cfv
    #
    cfv
    #
    vx
    cv
    #
    @1
    wcel
    #
    @4
    vs
    cv
    #
    @2
    cfv
    #
    wcel
    #
    vs
    cF
    wral
    #
    @0
    @4
    @3
    wcel
    #
    @5
    cJ
    ctop
    wcel
    cF
    cJ
    cuni
    #
    cfil
    cfv
    wcel
    @9
    @4
    cF
    cJ
    @11
    vs
    @11
    eqid
    isfcls
    simp3bi
    @8
    @10
    vs
    cS
    cF
    @6
    cS
    wceq
    @7
    @3
    @4
    @6
    cS
    @2
    fveq2
    eleq2d
    rspcv
    syl5
    ssrdv
end
