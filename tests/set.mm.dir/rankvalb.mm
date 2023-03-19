include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "crnk.mm"
include "wceq.mm"
include "elex.mm"
include "wrex.mm"
include "rankwflemb.mm"
include "intexrab.mm"
include "sylbb.mm"
include "eleq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "df-rank.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem rankvalb
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. U. ( R1 " On ) -> ( rank ` A ) = |^| { x e. On | A e. ( R1 ` suc x ) } )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cA
    cvv
    wcel
    cA
    vx
    cv
    csuc
    cr1
    cfv
    #
    wcel
    #
    vx
    con0
    crab
    #
    cint
    #
    cvv
    wcel
    #
    cA
    crnk
    cfv
    @5
    wceq
    cA
    @0
    elex
    @1
    @3
    vx
    con0
    wrex
    @6
    vx
    cA
    rankwflemb
    @3
    vx
    con0
    intexrab
    sylbb
    vy
    cA
    vy
    cv
    #
    @2
    wcel
    #
    vx
    con0
    crab
    #
    cint
    @5
    cvv
    cvv
    crnk
    @7
    cA
    wceq
    #
    @9
    @4
    @10
    @8
    @3
    vx
    con0
    @7
    cA
    @2
    eleq1
    rabbidv
    inteqd
    vy
    vx
    df-rank
    fvmptg
    syl2anc
end
