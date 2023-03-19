include "cfcls.mm"
include "co.mm"
include "wcel.mm"
include "ctop.mm"
include "cfil.mm"
include "cfv.mm"
include "cv.mm"
include "ccl.mm"
include "wral.mm"
include "isfcls.mm"
include "simp2bi.mm"

theorem fclsfil
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vs: setvar s
  let vt: setvar t
  let cY: class Y
  assume fclsval.x: |- X = U. J


  assert |- ( A e. ( J fClus F ) -> F e. ( Fil ` X ) )

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
    cX
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
    cX
    vs
    fclsval.x
    isfcls
    simp2bi
end
