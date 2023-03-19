include "ctop.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "ccld.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "ccl.mm"
include "cvv.mm"
include "elpwi.mm"
include "wa.mm"
include "clsval.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "sylan2.mm"
include "clsfval.mm"
include "clscld.mm"
include "fmpt2d.mm"

theorem clsf
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cS: class S
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( J e. Top -> ( cls ` J ) : ~P X --> ( Clsd ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    vx
    vy
    cX
    cpw
    #
    vx
    cv
    #
    vy
    cv
    #
    wss
    vy
    cJ
    ccld
    cfv
    #
    crab
    cint
    #
    @4
    cJ
    ccl
    cfv
    #
    cvv
    @2
    @1
    wcel
    @0
    @2
    cX
    wss
    #
    @5
    cvv
    wcel
    @2
    cX
    elpwi
    @0
    @7
    wa
    @5
    @2
    @6
    cfv
    cvv
    vy
    @2
    cJ
    cX
    clscld.1
    clsval
    @2
    @6
    fvex
    syl6eqelr
    sylan2
    vx
    vy
    cJ
    cX
    clscld.1
    clsfval
    @3
    @1
    wcel
    @0
    @3
    cX
    wss
    @3
    @6
    cfv
    @4
    wcel
    @3
    cX
    elpwi
    @3
    cJ
    cX
    clscld.1
    clscld
    sylan2
    fmpt2d
end
