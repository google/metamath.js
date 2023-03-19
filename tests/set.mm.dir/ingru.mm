include "cgru.mm"
include "wcel.mm"
include "wtr.mm"
include "cv.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "wf.mm"
include "crn.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "cmap.mm"
include "co.mm"
include "elgrug.mm"
include "ibi.mm"
include "trin.mm"
include "ex.mm"
include "wss.mm"
include "inss1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "inss2.mm"
include "elin.mm"
include "simplbi2.mm"
include "ral2imi.mm"
include "syl2im.mm"
include "im2anan9.mm"
include "cvv.mm"
include "vex.mm"
include "mapss.mm"
include "mp2an.mm"
include "inex1.mm"
include "elmap.mm"
include "fss.mm"
include "mpan2.mm"
include "sylbi.mm"
include "imim1i.mm"
include "alimi.mm"
include "df-ral.mm"
include "sylibr.mm"
include "3impa.mm"
include "df-3an.mm"
include "3imtr4g.mm"
include "syl.mm"
include "wb.mm"
include "syl6ibr.mm"
include "vtoclga.mm"
include "com12.mm"

theorem ingru
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cU: class U
  let vu: setvar u

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint U u
  assert |- ( ( Tr A /\ A. x e. A ( ~P x e. A /\ A. y e. A { x , y } e. A /\ A. y ( y : x --> A -> U. ran y e. A ) ) ) -> ( U e. Univ -> ( U i^i A ) e. Univ ) )

  proof
    cU
    cgru
    wcel
    cA
    wtr
    #
    vx
    cv
    #
    cpw
    #
    cA
    wcel
    #
    @1
    vy
    cv
    #
    cpr
    #
    cA
    wcel
    #
    vy
    cA
    wral
    #
    @1
    cA
    @4
    wf
    #
    @4
    crn
    cuni
    #
    cA
    wcel
    #
    wi
    #
    vy
    wal
    #
    w3a
    #
    vx
    cA
    wral
    #
    wa
    #
    cU
    cA
    cin
    #
    cgru
    wcel
    #
    @15
    vu
    cv
    #
    cA
    cin
    #
    cgru
    wcel
    #
    wi
    @15
    @17
    wi
    vu
    cU
    cgru
    @18
    cU
    wceq
    #
    @20
    @17
    @15
    @21
    @19
    @16
    cgru
    @18
    cU
    cA
    ineq1
    eleq1d
    imbi2d
    @18
    cgru
    wcel
    #
    @15
    @19
    wtr
    #
    @2
    @19
    wcel
    #
    @5
    @19
    wcel
    #
    vy
    @19
    wral
    #
    @9
    @19
    wcel
    #
    vy
    @19
    @1
    cmap
    co
    #
    wral
    #
    w3a
    #
    vx
    @19
    wral
    #
    wa
    #
    @20
    @22
    @18
    wtr
    #
    @2
    @18
    wcel
    #
    @5
    @18
    wcel
    #
    vy
    @18
    wral
    #
    @9
    @18
    wcel
    #
    vy
    @18
    @1
    cmap
    co
    #
    wral
    #
    w3a
    #
    vx
    @18
    wral
    #
    wa
    #
    @15
    @32
    wi
    @22
    @42
    vx
    vy
    @18
    cgru
    elgrug
    ibi
    @33
    @0
    @23
    @41
    @14
    @31
    @33
    @0
    @23
    @18
    cA
    trin
    ex
    @41
    @40
    vx
    @19
    wral
    #
    @14
    @13
    vx
    @19
    wral
    #
    @31
    @19
    @18
    wss
    #
    @41
    @43
    wi
    @18
    cA
    inss1
    #
    @40
    vx
    @19
    @18
    ssralv
    ax-mp
    @19
    cA
    wss
    #
    @14
    @44
    wi
    @18
    cA
    inss2
    #
    @13
    vx
    @19
    cA
    ssralv
    ax-mp
    @40
    @13
    @30
    vx
    @19
    @40
    @3
    @7
    wa
    #
    @12
    wa
    #
    @24
    @26
    wa
    #
    @29
    wa
    #
    @13
    @30
    @34
    @36
    @39
    @50
    @52
    wi
    @34
    @36
    wa
    @49
    @51
    @39
    @12
    @29
    @34
    @3
    @24
    @36
    @7
    @26
    @24
    @34
    @3
    @2
    @18
    cA
    elin
    simplbi2
    @36
    @35
    vy
    @19
    wral
    #
    @7
    @6
    vy
    @19
    wral
    #
    @26
    @45
    @36
    @53
    wi
    @46
    @35
    vy
    @19
    @18
    ssralv
    ax-mp
    @47
    @7
    @54
    wi
    @48
    @6
    vy
    @19
    cA
    ssralv
    ax-mp
    @35
    @6
    @25
    vy
    @19
    @25
    @35
    @6
    @5
    @18
    cA
    elin
    simplbi2
    ral2imi
    syl2im
    im2anan9
    @39
    @37
    vy
    @28
    wral
    #
    @12
    @10
    vy
    @28
    wral
    #
    @29
    @28
    @38
    wss
    #
    @39
    @55
    wi
    @18
    cvv
    wcel
    @45
    @57
    vu
    vex
    #
    @46
    @19
    @18
    @1
    cvv
    mapss
    mp2an
    @37
    vy
    @28
    @38
    ssralv
    ax-mp
    @12
    @4
    @28
    wcel
    #
    @10
    wi
    #
    vy
    wal
    @56
    @11
    @60
    vy
    @59
    @8
    @10
    @59
    @1
    @19
    @4
    wf
    #
    @8
    @19
    @1
    @4
    @18
    cA
    @58
    inex1
    #
    vx
    vex
    elmap
    @61
    @47
    @8
    @48
    @1
    @19
    cA
    @4
    fss
    mpan2
    sylbi
    imim1i
    alimi
    @10
    vy
    @28
    df-ral
    sylibr
    @37
    @10
    @27
    vy
    @28
    @27
    @37
    @10
    @9
    @18
    cA
    elin
    simplbi2
    ral2imi
    syl2im
    im2anan9
    3impa
    @3
    @7
    @12
    df-3an
    @24
    @26
    @29
    df-3an
    3imtr4g
    ral2imi
    syl2im
    im2anan9
    syl
    @19
    cvv
    wcel
    @20
    @32
    wb
    @62
    vx
    vy
    @19
    cvv
    elgrug
    ax-mp
    syl6ibr
    vtoclga
    com12
end
