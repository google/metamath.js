include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "ccld.mm"
include "wceq.mm"
include "clscld.mm"
include "wb.mm"
include "clsss3.mm"
include "iscld3.mm"
include "syldan.mm"
include "mpbid.mm"

theorem clsidm
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


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( cls ` J ) ` ( ( cls ` J ) ` S ) ) = ( ( cls ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    cS
    cJ
    ccl
    cfv
    #
    cfv
    #
    cJ
    ccld
    cfv
    wcel
    #
    @3
    @2
    cfv
    @3
    wceq
    #
    cS
    cJ
    cX
    clscld.1
    clscld
    @0
    @1
    @3
    cX
    wss
    @4
    @5
    wb
    cS
    cJ
    cX
    clscld.1
    clsss3
    @3
    cJ
    cX
    clscld.1
    iscld3
    syldan
    mpbid
end
