include "wfun.mm"
include "cdm.mm"
include "wfn.mm"
include "ccnv.mm"
include "cuni.mm"
include "cima.mm"
include "cv.mm"
include "ciun.mm"
include "wceq.mm"
include "funfn.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "wrex.mm"
include "wb.mm"
include "r19.42v.mm"
include "bicomi.mm"
include "a1i.mm"
include "eluni2.mm"
include "anbi2i.mm"
include "elpreima.mm"
include "rexbidv.mm"
include "3bitr4d.mm"
include "eliun.mm"
include "eqrdv.mm"
include "sylbi.mm"

theorem unipreima
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y

  disjoint F x
  disjoint A x
  disjoint x y
  disjoint F y
  disjoint A y
  assert |- ( Fun F -> ( `' F " U. A ) = U_ x e. A ( `' F " x ) )

  proof
    cF
    wfun
    cF
    cF
    cdm
    #
    wfn
    #
    cF
    ccnv
    #
    cA
    cuni
    #
    cima
    #
    vx
    cA
    @2
    vx
    cv
    #
    cima
    #
    ciun
    #
    wceq
    cF
    funfn
    @1
    vy
    @4
    @7
    @1
    vy
    cv
    #
    @0
    wcel
    #
    @8
    cF
    cfv
    #
    @3
    wcel
    #
    wa
    #
    @8
    @6
    wcel
    #
    vx
    cA
    wrex
    #
    @8
    @4
    wcel
    @8
    @7
    wcel
    #
    @1
    @9
    @10
    @5
    wcel
    #
    vx
    cA
    wrex
    #
    wa
    #
    @9
    @16
    wa
    #
    vx
    cA
    wrex
    #
    @12
    @14
    @18
    @20
    wb
    @1
    @20
    @18
    @9
    @16
    vx
    cA
    r19.42v
    bicomi
    a1i
    @12
    @18
    wb
    @1
    @11
    @17
    @9
    vx
    @10
    cA
    eluni2
    anbi2i
    a1i
    @1
    @13
    @19
    vx
    cA
    @0
    @8
    @5
    cF
    elpreima
    rexbidv
    3bitr4d
    @0
    @8
    @3
    cF
    elpreima
    @15
    @14
    wb
    @1
    vx
    @8
    cA
    @6
    eliun
    a1i
    3bitr4d
    eqrdv
    sylbi
end
