include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "dff13f.mm"
include "fmpt.mm"
include "anbi1i.mm"
include "wb.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "raaanv.mm"
include "fvmpt2.mm"
include "fvmptg.mm"
include "eqeqan12d.mm"
include "an4s.mm"
include "imbi1d.mm"
include "ex.mm"
include "ralimdva.mm"
include "ralbi.mm"
include "syl6.mm"
include "ralimia.mm"
include "syl.mm"
include "sylbir.mm"
include "sylan2b.mm"
include "anidms.mm"
include "pm5.32i.mm"
include "3bitr2i.mm"

theorem f1mpt
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume f1mpt.1: |- F = ( x e. A |-> C )
  assume f1mpt.2: |- ( x = y -> C = D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint F y
  assert |- ( F : A -1-1-> B <-> ( A. x e. A C e. B /\ A. x e. A A. y e. A ( C = D -> x = y ) ) )

  proof
    cA
    cB
    cF
    wf1
    cA
    cB
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @1
    @3
    wceq
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    cC
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @9
    wa
    @11
    cC
    cD
    wceq
    #
    @6
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    vx
    vy
    cA
    cB
    cF
    vx
    cF
    vx
    cA
    cC
    cmpt
    f1mpt.1
    vx
    cA
    cC
    nfmpt1
    nfcxfr
    vy
    cF
    nfcv
    dff13f
    @11
    @0
    @9
    vx
    cA
    cB
    cC
    cF
    f1mpt.1
    fmpt
    anbi1i
    @11
    @9
    @15
    @11
    @9
    @15
    wb
    #
    @11
    @11
    cD
    cB
    wcel
    #
    vy
    cA
    wral
    #
    @16
    @10
    @17
    vx
    vy
    cA
    @6
    cC
    cD
    cB
    f1mpt.2
    eleq1d
    cbvralv
    @11
    @18
    wa
    @10
    @17
    wa
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @16
    @10
    @17
    vx
    vy
    cA
    raaanv
    @21
    @8
    @14
    wb
    #
    vx
    cA
    wral
    @16
    @20
    @22
    vx
    cA
    @1
    cA
    wcel
    #
    @20
    @7
    @13
    wb
    #
    vy
    cA
    wral
    @22
    @23
    @19
    @24
    vy
    cA
    @23
    @3
    cA
    wcel
    #
    wa
    #
    @19
    @24
    @26
    @19
    wa
    @5
    @12
    @6
    @23
    @10
    @25
    @17
    @5
    @12
    wb
    @23
    @10
    wa
    @25
    @17
    wa
    @2
    cC
    @4
    cD
    vx
    cA
    cC
    cB
    cF
    f1mpt.1
    fvmpt2
    vx
    @3
    cC
    cD
    cA
    cB
    cF
    f1mpt.2
    f1mpt.1
    fvmptg
    eqeqan12d
    an4s
    imbi1d
    ex
    ralimdva
    @7
    @13
    vy
    cA
    ralbi
    syl6
    ralimia
    @8
    @14
    vx
    cA
    ralbi
    syl
    sylbir
    sylan2b
    anidms
    pm5.32i
    3bitr2i
end
