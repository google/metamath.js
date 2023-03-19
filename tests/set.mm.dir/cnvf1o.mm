include "wrel.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cuni.mm"
include "cmpt.mm"
include "cvv.mm"
include "eqid.mm"
include "wcel.mm"
include "wa.mm"
include "snex.mm"
include "cnvex.mm"
include "uniex.mm"
include "a1i.mm"
include "wceq.mm"
include "cnvf1olem.mm"
include "relcnv.mm"
include "simpr.mm"
include "sylancr.mm"
include "wb.mm"
include "dfrel2.mm"
include "eleq2.mm"
include "sylbi.mm"
include "anbi1d.mm"
include "adantr.mm"
include "mpbid.mm"
include "impbida.mm"
include "f1od.mm"

theorem cnvf1o
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( Rel A -> ( x e. A |-> U. `' { x } ) : A -1-1-onto-> `' A )

  proof
    cA
    wrel
    #
    vx
    vy
    cA
    cA
    ccnv
    #
    vx
    cv
    #
    csn
    #
    ccnv
    #
    cuni
    #
    vy
    cv
    #
    csn
    #
    ccnv
    #
    cuni
    #
    vx
    cA
    @5
    cmpt
    #
    cvv
    cvv
    @10
    eqid
    @5
    cvv
    wcel
    @0
    @2
    cA
    wcel
    #
    wa
    @4
    @3
    @2
    snex
    cnvex
    uniex
    a1i
    @9
    cvv
    wcel
    @0
    @6
    @1
    wcel
    #
    wa
    @8
    @7
    @6
    snex
    cnvex
    uniex
    a1i
    @0
    @11
    @6
    @5
    wceq
    #
    wa
    #
    @12
    @2
    @9
    wceq
    wa
    #
    cA
    @2
    @6
    cnvf1olem
    @0
    @15
    wa
    #
    @2
    @1
    ccnv
    #
    wcel
    #
    @13
    wa
    #
    @14
    @16
    @1
    wrel
    @15
    @19
    cA
    relcnv
    @0
    @15
    simpr
    @1
    @6
    @2
    cnvf1olem
    sylancr
    @0
    @19
    @14
    wb
    @15
    @0
    @18
    @11
    @13
    @0
    @17
    cA
    wceq
    @18
    @11
    wb
    cA
    dfrel2
    @17
    cA
    @2
    eleq2
    sylbi
    anbi1d
    adantr
    mpbid
    impbida
    f1od
end
