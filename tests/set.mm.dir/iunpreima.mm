include "wfun.mm"
include "ccnv.mm"
include "ciun.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "crab.mm"
include "wrex.mm"
include "wb.mm"
include "eliun.mm"
include "a1i.mm"
include "rabbidv.mm"
include "wfn.mm"
include "wceq.mm"
include "funfn.mm"
include "fncnvima2.mm"
include "sylbi.mm"
include "iunrab.mm"
include "3eqtr4d.mm"
include "iuneq2d.mm"
include "eqtr4d.mm"

theorem iunpreima
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  assert |- ( Fun F -> ( `' F " U_ x e. A B ) = U_ x e. A ( `' F " B ) )

  proof
    cF
    wfun
    #
    cF
    ccnv
    #
    vx
    cA
    cB
    ciun
    #
    cima
    #
    vx
    cA
    vy
    cv
    cF
    cfv
    #
    cB
    wcel
    #
    vy
    cF
    cdm
    #
    crab
    #
    ciun
    #
    vx
    cA
    @1
    cB
    cima
    #
    ciun
    @0
    @4
    @2
    wcel
    #
    vy
    @6
    crab
    #
    @5
    vx
    cA
    wrex
    #
    vy
    @6
    crab
    #
    @3
    @8
    @0
    @10
    @12
    vy
    @6
    @10
    @12
    wb
    @0
    vx
    @4
    cA
    cB
    eliun
    a1i
    rabbidv
    @0
    cF
    @6
    wfn
    #
    @3
    @11
    wceq
    cF
    funfn
    #
    vy
    @6
    @2
    cF
    fncnvima2
    sylbi
    @8
    @13
    wceq
    @0
    @5
    vx
    vy
    cA
    @6
    iunrab
    a1i
    3eqtr4d
    @0
    vx
    cA
    @9
    @7
    @0
    @14
    @9
    @7
    wceq
    @15
    vy
    @6
    cB
    cF
    fncnvima2
    sylbi
    iuneq2d
    eqtr4d
end
