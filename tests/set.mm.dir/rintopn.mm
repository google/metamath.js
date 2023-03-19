include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "w3a.mm"
include "cint.mm"
include "cin.mm"
include "cv.mm"
include "ciin.mm"
include "intiin.mm"
include "ineq2i.mm"
include "wral.mm"
include "dfss3.mm"
include "riinopn.mm"
include "3com23.mm"
include "syl3an2b.mm"
include "syl5eqel.mm"

theorem rintopn
  let cA: class A
  let cJ: class J
  let cX: class X
  let vx: setvar x
  assume 1open.1: |- X = U. J


  assert |- ( ( J e. Top /\ A C_ J /\ A e. Fin ) -> ( X i^i |^| A ) e. J )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cJ
    wss
    #
    cA
    cfn
    wcel
    #
    w3a
    cX
    cA
    cint
    #
    cin
    cX
    vx
    cA
    vx
    cv
    #
    ciin
    #
    cin
    #
    cJ
    @3
    @5
    cX
    vx
    cA
    intiin
    ineq2i
    @1
    @0
    @4
    cJ
    wcel
    vx
    cA
    wral
    #
    @2
    @6
    cJ
    wcel
    #
    vx
    cA
    cJ
    dfss3
    @0
    @2
    @7
    @8
    vx
    cA
    @4
    cJ
    cX
    1open.1
    riinopn
    3com23
    syl3an2b
    syl5eqel
end
