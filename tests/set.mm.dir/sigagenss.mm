include "cuni.mm"
include "csiga.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "csigagen.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "cvv.mm"
include "wceq.mm"
include "ssexg.mm"
include "ancoms.mm"
include "sigagenval.mm"
include "syl.mm"
include "sseq2.mm"
include "intminss.mm"
include "eqsstrd.mm"

theorem sigagenss
  let cA: class A
  let cS: class S
  let vs: setvar s


  assert |- ( ( S e. ( sigAlgebra ` U. A ) /\ A C_ S ) -> ( sigaGen ` A ) C_ S )

  proof
    cS
    cA
    cuni
    csiga
    cfv
    #
    wcel
    #
    cA
    cS
    wss
    #
    wa
    #
    cA
    csigagen
    cfv
    #
    cA
    vs
    cv
    #
    wss
    #
    vs
    @0
    crab
    cint
    #
    cS
    @3
    cA
    cvv
    wcel
    #
    @4
    @7
    wceq
    @2
    @1
    @8
    cA
    cS
    @0
    ssexg
    ancoms
    cA
    cvv
    vs
    sigagenval
    syl
    @6
    @2
    vs
    cS
    @0
    @5
    cS
    cA
    sseq2
    intminss
    eqsstrd
end
