include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "weq.mm"
include "cv.mm"
include "csb.mm"
include "wo.mm"
include "cun.mm"
include "wral.mm"
include "wa.mm"
include "wdisj.mm"
include "w3a.mm"
include "wcel.mm"
include "wn.mm"
include "wb.mm"
include "disjel.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "con2d.mm"
include "impr.mm"
include "biorf.mm"
include "syl.mm"
include "bicomd.mm"
include "2ralbidva.mm"
include "anbi2d.mm"
include "ralunb.mm"
include "ralbii.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfin.mm"
include "nfeq1.mm"
include "nfor.mm"
include "nfral.mm"
include "equequ2.mm"
include "csbhypf.mm"
include "ineq2d.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "cbvralv.mm"
include "equequ1.mm"
include "csbeq1a.mm"
include "ineq1d.mm"
include "ralbidv.mm"
include "syl5bbr.mm"
include "cbvral.mm"
include "r19.26.mm"
include "3bitr3i.mm"
include "disjor.mm"
include "anbi1i.mm"
include "3bitr4g.mm"
include "equcom.mm"
include "syl6bb.mm"
include "incom.mm"
include "syl6eq.mm"
include "ralcom.mm"
include "bitri.mm"
include "syl5bb.mm"
include "anbi1d.mm"
include "disjors.mm"
include "anbi2ci.mm"
include "anbi12d.mm"
include "df-3an.mm"
include "anandir.mm"

theorem disjxun
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vz: setvar z
  assume disjxun.1: |- ( x = y -> C = D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B w
  disjoint B z
  disjoint C w
  disjoint C z
  disjoint D w
  disjoint D z
  assert |- ( ( A i^i B ) = (/) -> ( Disj_ x e. ( A u. B ) C <-> ( Disj_ x e. A C /\ Disj_ x e. B C /\ A. x e. A A. y e. B ( C i^i D ) = (/) ) ) )

  proof
    cA
    cB
    cin
    c0
    wceq
    #
    vz
    vw
    weq
    #
    vx
    vz
    cv
    #
    cC
    csb
    #
    vx
    vw
    cv
    #
    cC
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vw
    cA
    cB
    cun
    #
    wral
    #
    vz
    cA
    wral
    #
    @10
    vz
    cB
    wral
    #
    wa
    #
    vx
    cA
    cC
    wdisj
    #
    cC
    cD
    cin
    #
    c0
    wceq
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    wa
    #
    vx
    cB
    cC
    wdisj
    #
    @17
    wa
    #
    wa
    #
    vx
    @9
    cC
    wdisj
    #
    @14
    @19
    @17
    w3a
    #
    @0
    @11
    @18
    @12
    @20
    @0
    vx
    vy
    weq
    #
    @16
    wo
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @25
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    wa
    #
    @27
    @17
    wa
    @11
    @18
    @0
    @29
    @17
    @27
    @0
    @25
    @16
    vx
    vy
    cA
    cB
    @0
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    wa
    #
    @16
    @25
    @35
    @24
    wn
    #
    @16
    @25
    wb
    @0
    @32
    @34
    @36
    @0
    @32
    wa
    #
    @24
    @34
    @37
    @31
    cB
    wcel
    #
    wn
    @24
    @34
    wn
    cA
    cB
    @31
    disjel
    @24
    @38
    @34
    @31
    @33
    cB
    eleq1
    notbid
    syl5ibcom
    con2d
    impr
    @24
    @16
    biorf
    syl
    bicomd
    2ralbidva
    #
    anbi2d
    @25
    vy
    @9
    wral
    #
    vx
    cA
    wral
    @26
    @28
    wa
    #
    vx
    cA
    wral
    @11
    @30
    @40
    @41
    vx
    cA
    @25
    vy
    cA
    cB
    ralunb
    ralbii
    @40
    @10
    vx
    vz
    cA
    @40
    vz
    nfv
    @8
    vx
    vw
    @9
    vx
    @9
    nfcv
    @1
    @7
    vx
    @1
    vx
    nfv
    vx
    @6
    c0
    vx
    @3
    @5
    vx
    @2
    cC
    nfcsb1v
    vx
    @4
    cC
    nfcsb1v
    nfin
    nfeq1
    nfor
    #
    nfral
    @40
    vx
    vw
    weq
    #
    cC
    @5
    cin
    #
    c0
    wceq
    #
    wo
    #
    vw
    @9
    wral
    vx
    vz
    weq
    #
    @10
    @46
    @25
    vw
    vy
    @9
    vw
    vy
    weq
    #
    @43
    @24
    @45
    @16
    vw
    vy
    vx
    equequ2
    @48
    @44
    @15
    c0
    @48
    @5
    cD
    cC
    vx
    vw
    @33
    cC
    cD
    vx
    @33
    nfcv
    #
    vx
    cD
    nfcv
    #
    disjxun.1
    csbhypf
    ineq2d
    eqeq1d
    orbi12d
    cbvralv
    @47
    @46
    @8
    vw
    @9
    @47
    @43
    @1
    @45
    @7
    vx
    vz
    vw
    equequ1
    @47
    @44
    @6
    c0
    @47
    cC
    @3
    @5
    vx
    @2
    cC
    csbeq1a
    ineq1d
    eqeq1d
    orbi12d
    ralbidv
    syl5bbr
    cbvral
    @26
    @28
    vx
    cA
    r19.26
    3bitr3i
    @14
    @27
    @17
    cA
    cC
    cD
    vx
    vy
    disjxun.1
    disjor
    anbi1i
    3bitr4g
    @0
    @8
    vw
    cA
    wral
    #
    vz
    cB
    wral
    #
    @8
    vw
    cB
    wral
    #
    vz
    cB
    wral
    #
    wa
    #
    @17
    @54
    wa
    @12
    @20
    @0
    @52
    @17
    @54
    @52
    @29
    @0
    @17
    @52
    @25
    vx
    cA
    wral
    #
    vy
    cB
    wral
    @29
    @51
    @56
    vz
    vy
    cB
    @51
    vz
    vx
    weq
    #
    @3
    cC
    cin
    #
    c0
    wceq
    #
    wo
    #
    vx
    cA
    wral
    vz
    vy
    weq
    #
    @56
    @60
    @8
    vx
    vw
    cA
    @60
    vw
    nfv
    @42
    @43
    @57
    @1
    @59
    @7
    vx
    vw
    vz
    equequ2
    @43
    @58
    @6
    c0
    @43
    cC
    @5
    @3
    vx
    @4
    cC
    csbeq1a
    ineq2d
    eqeq1d
    orbi12d
    cbvral
    @61
    @60
    @25
    vx
    cA
    @61
    @57
    @24
    @59
    @16
    @61
    @57
    vy
    vx
    weq
    @24
    vz
    vy
    vx
    equequ1
    vy
    vx
    equcom
    syl6bb
    @61
    @58
    @15
    c0
    @61
    @58
    cD
    cC
    cin
    @15
    @61
    @3
    cD
    cC
    vx
    vz
    @33
    cC
    cD
    @49
    @50
    disjxun.1
    csbhypf
    ineq1d
    cD
    cC
    incom
    syl6eq
    eqeq1d
    orbi12d
    ralbidv
    syl5bbr
    cbvralv
    @25
    vy
    vx
    cB
    cA
    ralcom
    bitri
    @39
    syl5bb
    anbi1d
    @12
    @51
    @53
    wa
    #
    vz
    cB
    wral
    @55
    @10
    @62
    vz
    cB
    @8
    vw
    cA
    cB
    ralunb
    ralbii
    @51
    @53
    vz
    cB
    r19.26
    bitri
    @19
    @54
    @17
    vx
    cB
    cC
    vz
    vw
    disjors
    anbi2ci
    3bitr4g
    anbi12d
    @22
    @10
    vz
    @9
    wral
    @13
    vx
    @9
    cC
    vz
    vw
    disjors
    @10
    vz
    cA
    cB
    ralunb
    bitri
    @23
    @14
    @19
    wa
    @17
    wa
    @21
    @14
    @19
    @17
    df-3an
    @14
    @19
    @17
    anandir
    bitri
    3bitr4g
end
