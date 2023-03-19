include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "isnum2.mm"
include "rabn0.mm"
include "intex.mm"
include "3bitr2i.mm"
include "biimpi.mm"
include "breq2.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "df-card.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem cardval3
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. dom card -> ( card ` A ) = |^| { x e. On | x ~~ A } )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cA
    cvv
    wcel
    vx
    cv
    #
    cA
    cen
    wbr
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
    ccrd
    cfv
    @5
    wceq
    cA
    @0
    elex
    @1
    @6
    @1
    @3
    vx
    con0
    wrex
    @4
    c0
    wne
    @6
    vx
    cA
    isnum2
    @3
    vx
    con0
    rabn0
    @4
    intex
    3bitr2i
    biimpi
    vy
    cA
    @2
    vy
    cv
    #
    cen
    wbr
    #
    vx
    con0
    crab
    #
    cint
    @5
    cvv
    cvv
    ccrd
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
    cen
    breq2
    rabbidv
    inteqd
    vy
    vx
    df-card
    fvmptg
    syl2anc
end
