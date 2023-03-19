include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "ccld.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "ccl.mm"
include "ssintub.mm"
include "clsval.mm"
include "syl5sseqr.mm"

theorem sscls
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> S C_ ( ( cls ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    cS
    vx
    cv
    wss
    vx
    cJ
    ccld
    cfv
    #
    crab
    cint
    cS
    cS
    cJ
    ccl
    cfv
    cfv
    vx
    cS
    @0
    ssintub
    vx
    cS
    cJ
    cX
    clscld.1
    clsval
    syl5sseqr
end
