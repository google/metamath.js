include "cfcls.mm"
include "co.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "cfil.mm"
include "cfv.mm"
include "cv.mm"
include "ccl.mm"
include "wral.mm"
include "eqid.mm"
include "isfcls.mm"
include "simp1bi.mm"

theorem fclstop
  let cA: class A
  let cF: class F
  let cJ: class J
  let vo: setvar o
  let vs: setvar s
  let cU: class U
  let cS: class S
  let cX: class X


  assert |- ( A e. ( J fClus F ) -> J e. Top )

  proof
    cA
    cJ
    cF
    cfcls
    co
    wcel
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
    cA
    vs
    cv
    cJ
    ccl
    cfv
    cfv
    wcel
    vs
    cF
    wral
    cA
    cF
    cJ
    @0
    vs
    @0
    eqid
    isfcls
    simp1bi
end
