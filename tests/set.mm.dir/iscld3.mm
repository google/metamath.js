include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccld.mm"
include "cfv.mm"
include "ccl.mm"
include "wceq.mm"
include "cldcls.mm"
include "clscld.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "impbid2.mm"

theorem iscld3
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( S e. ( Clsd ` J ) <-> ( ( cls ` J ) ` S ) = S ) )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    #
    cS
    cJ
    ccld
    cfv
    #
    wcel
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cS
    wceq
    #
    cS
    cJ
    cldcls
    @0
    @3
    @1
    wcel
    @4
    @2
    cS
    cJ
    cX
    clscld.1
    clscld
    @3
    cS
    @1
    eleq1
    syl5ibcom
    impbid2
end
