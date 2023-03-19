include "cop.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "wbr.mm"
include "df-br.mm"
include "wrel.mm"
include "wral.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "brrelexi.mm"
include "sylbir.mm"
include "elex.mm"
include "adantr.mm"
include "wb.mm"
include "nfiu1.mm"
include "nfel2.mm"
include "nfv.mm"
include "nfbi.mm"
include "wceq.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "eleq1.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "bibi12d.mm"
include "opeliunxp.mm"
include "vtoclg1f.mm"
include "pm5.21nii.mm"

theorem opeliunxp2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let vy: setvar y
  assume opeliunxp2.1: |- ( x = C -> B = E )

  disjoint C x
  disjoint D x
  disjoint E x
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint x y
  disjoint C y
  assert |- ( <. C , D >. e. U_ x e. A ( { x } X. B ) <-> ( C e. A /\ D e. E ) )

  proof
    cC
    cD
    cop
    #
    vx
    cA
    vx
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    wcel
    #
    cC
    cvv
    wcel
    #
    cC
    cA
    wcel
    #
    cD
    cE
    wcel
    #
    wa
    #
    @5
    cC
    cD
    @4
    wbr
    @6
    cC
    cD
    @4
    df-br
    cC
    cD
    @4
    @4
    wrel
    @3
    wrel
    #
    vx
    cA
    wral
    @10
    vx
    cA
    @2
    cB
    relxp
    rgenw
    vx
    cA
    @3
    reliun
    mpbir
    brrelexi
    sylbir
    @7
    @6
    @8
    cC
    cA
    elex
    adantr
    @1
    cD
    cop
    #
    @4
    wcel
    #
    @1
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    wa
    #
    wb
    @5
    @9
    wb
    vx
    cC
    cvv
    @5
    @9
    vx
    vx
    @0
    @4
    vx
    cA
    @3
    nfiu1
    nfel2
    @9
    vx
    nfv
    nfbi
    @1
    cC
    wceq
    #
    @12
    @5
    @15
    @9
    @16
    @11
    @0
    @4
    @1
    cC
    cD
    opeq1
    eleq1d
    @16
    @13
    @7
    @14
    @8
    @1
    cC
    cA
    eleq1
    @16
    cB
    cE
    cD
    opeliunxp2.1
    eleq2d
    anbi12d
    bibi12d
    vx
    cA
    cB
    cD
    opeliunxp
    vtoclg1f
    pm5.21nii
end
