include "wcel.mm"
include "csigagen.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "csiga.mm"
include "crab.mm"
include "cint.mm"
include "sigagenval.mm"
include "c0.mm"
include "wne.mm"
include "cpw.mm"
include "cvv.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "intex.mm"
include "sylibr.mm"
include "ssrab2.mm"
include "a1i.mm"
include "elpw2.mm"
include "insiga.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem sigagensiga
  let cA: class A
  let cV: class V
  let vs: setvar s


  assert |- ( A e. V -> ( sigaGen ` A ) e. ( sigAlgebra ` U. A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    csigagen
    cfv
    #
    cA
    vs
    cv
    wss
    #
    vs
    cA
    cuni
    #
    csiga
    cfv
    #
    crab
    #
    cint
    #
    @4
    cA
    cV
    vs
    sigagenval
    #
    @0
    @5
    c0
    wne
    #
    @5
    @4
    cpw
    wcel
    #
    @6
    @4
    wcel
    @0
    @6
    cvv
    wcel
    @8
    @0
    @6
    @1
    cvv
    @7
    cA
    csigagen
    fvex
    syl6eqelr
    @5
    intex
    sylibr
    @0
    @5
    @4
    wss
    #
    @9
    @10
    @0
    @2
    vs
    @4
    ssrab2
    a1i
    @5
    @4
    @3
    csiga
    fvex
    elpw2
    sylibr
    @5
    @3
    insiga
    syl2anc
    eqeltrd
end
