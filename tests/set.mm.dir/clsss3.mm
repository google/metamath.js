include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "ccld.mm"
include "clscld.mm"
include "cldss.mm"
include "syl.mm"

theorem clsss3
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( cls ` J ) ` S ) C_ X )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cJ
    ccld
    cfv
    wcel
    @0
    cX
    wss
    cS
    cJ
    cX
    clscld.1
    clscld
    @0
    cJ
    cX
    clscld.1
    cldss
    syl
end
