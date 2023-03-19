include "c0.mm"
include "wne.mm"
include "ciin.mm"
include "ccnv.mm"
include "wrel.mm"
include "wceq.mm"
include "relcnv.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "df-rel.mm"
include "mpbi.mm"
include "rgenw.mm"
include "r19.2z.mm"
include "mpan2.mm"
include "iinss.mm"
include "syl.mm"
include "sylibr.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "opex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "vex.mm"
include "opelcnv.mm"
include "ralbii.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "eqrelriv.mm"
include "sylancr.mm"

theorem cnviin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b

  disjoint A x
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint B a
  disjoint B b
  assert |- ( A =/= (/) -> `' |^|_ x e. A B = |^|_ x e. A `' B )

  proof
    cA
    c0
    wne
    #
    vx
    cA
    cB
    ciin
    #
    ccnv
    #
    wrel
    vx
    cA
    cB
    ccnv
    #
    ciin
    #
    wrel
    #
    @2
    @4
    wceq
    @1
    relcnv
    @0
    @4
    cvv
    cvv
    cxp
    #
    wss
    #
    @5
    @0
    @3
    @6
    wss
    #
    vx
    cA
    wrex
    #
    @7
    @0
    @8
    vx
    cA
    wral
    @9
    @8
    vx
    cA
    @3
    wrel
    @8
    cB
    relcnv
    @3
    df-rel
    mpbi
    rgenw
    @8
    vx
    cA
    r19.2z
    mpan2
    vx
    cA
    @3
    @6
    iinss
    syl
    @4
    df-rel
    sylibr
    va
    vb
    @2
    @4
    vb
    cv
    #
    va
    cv
    #
    cop
    #
    @1
    wcel
    #
    @12
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @11
    @10
    cop
    #
    @2
    wcel
    @16
    @4
    wcel
    #
    @12
    cvv
    wcel
    @13
    @15
    wb
    @10
    @11
    opex
    vx
    @12
    cA
    cB
    cvv
    eliin
    ax-mp
    @11
    @10
    @1
    va
    vex
    #
    vb
    vex
    #
    opelcnv
    @17
    @16
    @3
    wcel
    #
    vx
    cA
    wral
    #
    @15
    @16
    cvv
    wcel
    @17
    @21
    wb
    @11
    @10
    opex
    vx
    @16
    cA
    @3
    cvv
    eliin
    ax-mp
    @20
    @14
    vx
    cA
    @11
    @10
    cB
    @18
    @19
    opelcnv
    ralbii
    bitri
    3bitr4i
    eqrelriv
    sylancr
end
