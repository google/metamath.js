include "cpw.mm"
include "wss.mm"
include "wcel.mm"
include "cv.mm"
include "cint.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "cin.mm"
include "wb.mm"
include "wceq.mm"
include "cvv.mm"
include "ssv.mm"
include "int0.mm"
include "sseqtr4i.mm"
include "df-ss.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "a1i.mm"
include "wne.mm"
include "eldifsn.mm"
include "wi.mm"
include "sstr2.mm"
include "bj-intss.mm"
include "syl6.mm"
include "elpwi.mm"
include "syl11.mm"
include "impd.mm"
include "syl5bi.mm"
include "incom.mm"
include "eqeq1i.mm"
include "eqcom.mm"
include "sylbb.mm"
include "sylbi.mm"
include "eleq1.mm"
include "syl5.mm"
include "syld.mm"
include "ralrimiv.mm"
include "ralbi.mm"
include "syl.mm"
include "anbi12d.mm"
include "ancom.mm"
include "syl6bb.mm"
include "0elpw.mm"
include "inteq.mm"
include "ineq2.mm"
include "3syl.mm"
include "bj-raldifsn.mm"
include "ax-mp.mm"
include "syl6bbr.mm"

theorem bj-0int
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cX: class X

  disjoint A x
  disjoint B x
  disjoint X x
  assert |- ( A C_ ~P X -> ( ( X e. B /\ A. x e. ( ~P A \ { (/) } ) |^| x e. B ) <-> A. x e. ~P A ( X i^i |^| x ) e. B ) )

  proof
    cA
    cX
    cpw
    #
    wss
    #
    cX
    cB
    wcel
    #
    vx
    cv
    #
    cint
    #
    cB
    wcel
    #
    vx
    cA
    cpw
    #
    c0
    csn
    cdif
    #
    wral
    #
    wa
    #
    cX
    @4
    cin
    #
    cB
    wcel
    #
    vx
    @7
    wral
    #
    cX
    c0
    cint
    #
    cin
    #
    cB
    wcel
    #
    wa
    #
    @11
    vx
    @6
    wral
    #
    @1
    @9
    @15
    @12
    wa
    @16
    @1
    @2
    @15
    @8
    @12
    @2
    @15
    wb
    @1
    cX
    @14
    cB
    @14
    cX
    cX
    @13
    wss
    @14
    cX
    wceq
    cX
    cvv
    @13
    cX
    ssv
    int0
    sseqtr4i
    cX
    @13
    df-ss
    mpbi
    eqcomi
    eleq1i
    a1i
    @1
    @5
    @11
    wb
    #
    vx
    @7
    wral
    @8
    @12
    wb
    @1
    @18
    vx
    @7
    @1
    @3
    @7
    wcel
    #
    @4
    cX
    wss
    #
    @18
    @19
    @3
    @6
    wcel
    #
    @3
    c0
    wne
    #
    wa
    @1
    @20
    @3
    @6
    c0
    eldifsn
    @1
    @21
    @22
    @20
    @3
    cA
    wss
    #
    @1
    @22
    @20
    wi
    #
    @21
    @23
    @1
    @3
    @0
    wss
    @24
    @3
    cA
    @0
    sstr2
    @3
    cX
    bj-intss
    syl6
    @3
    cA
    elpwi
    syl11
    impd
    syl5bi
    @20
    @4
    @10
    wceq
    #
    @1
    @18
    @20
    @4
    cX
    cin
    #
    @4
    wceq
    #
    @25
    @4
    cX
    df-ss
    @27
    @10
    @4
    wceq
    @25
    @26
    @10
    @4
    @4
    cX
    incom
    eqeq1i
    @10
    @4
    eqcom
    sylbb
    sylbi
    @25
    @18
    wi
    @1
    @4
    @10
    cB
    eleq1
    a1i
    syl5
    syld
    ralrimiv
    @5
    @11
    vx
    @7
    ralbi
    syl
    anbi12d
    @15
    @12
    ancom
    syl6bb
    c0
    @6
    wcel
    @17
    @16
    wb
    cA
    0elpw
    @11
    @15
    vx
    @6
    c0
    @3
    c0
    wceq
    @4
    @13
    wceq
    @10
    @14
    wceq
    @11
    @15
    wb
    @3
    c0
    inteq
    @4
    @13
    cX
    ineq2
    @10
    @14
    cB
    eleq1
    3syl
    bj-raldifsn
    ax-mp
    syl6bbr
end
