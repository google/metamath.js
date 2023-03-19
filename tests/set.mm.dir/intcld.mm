include "c0.mm"
include "wne.mm"
include "ccld.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cint.mm"
include "cv.mm"
include "ciin.mm"
include "intiin.mm"
include "wcel.mm"
include "wral.mm"
include "dfss3.mm"
include "iincld.mm"
include "sylan2b.mm"
include "syl5eqel.mm"

theorem intcld
  let cA: class A
  let cJ: class J
  let vx: setvar x
  let cS: class S


  assert |- ( ( A =/= (/) /\ A C_ ( Clsd ` J ) ) -> |^| A e. ( Clsd ` J ) )

  proof
    cA
    c0
    wne
    #
    cA
    cJ
    ccld
    cfv
    #
    wss
    #
    wa
    cA
    cint
    vx
    cA
    vx
    cv
    #
    ciin
    #
    @1
    vx
    cA
    intiin
    @2
    @0
    @3
    @1
    wcel
    vx
    cA
    wral
    @4
    @1
    wcel
    vx
    cA
    @1
    dfss3
    vx
    cA
    @3
    cJ
    iincld
    sylan2b
    syl5eqel
end
