include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "ctsk.mm"
include "crab.mm"
include "cint.mm"
include "ctskm.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "wrex.mm"
include "cuni.mm"
include "grothtsk.mm"
include "syl6eleqr.mm"
include "eluni2.mm"
include "sylib.mm"
include "intexrab.mm"
include "eleq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "df-tskm.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem tskmval
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. V -> ( tarskiMap ` A ) = |^| { x e. Tarski | A e. x } )

  proof
    cA
    cV
    wcel
    #
    cA
    cvv
    wcel
    cA
    vx
    cv
    #
    wcel
    #
    vx
    ctsk
    crab
    #
    cint
    #
    cvv
    wcel
    #
    cA
    ctskm
    cfv
    @4
    wceq
    cA
    cV
    elex
    #
    @0
    @2
    vx
    ctsk
    wrex
    #
    @5
    @0
    cA
    ctsk
    cuni
    #
    wcel
    @7
    @0
    cA
    cvv
    @8
    @6
    grothtsk
    syl6eleqr
    vx
    cA
    ctsk
    eluni2
    sylib
    @2
    vx
    ctsk
    intexrab
    sylib
    vy
    cA
    vy
    cv
    #
    @1
    wcel
    #
    vx
    ctsk
    crab
    #
    cint
    @4
    cvv
    cvv
    ctskm
    @9
    cA
    wceq
    #
    @11
    @3
    @12
    @10
    @2
    vx
    ctsk
    @9
    cA
    @1
    eleq1
    rabbidv
    inteqd
    vy
    vx
    df-tskm
    fvmptg
    syl2anc
end
