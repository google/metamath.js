include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cconn.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cin.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "cuni.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "eqid.mm"
include "simpll.mm"
include "simplrl.mm"
include "simpr1.mm"
include "simplrr.mm"
include "simpr2.mm"
include "simpr3.mm"
include "conndisj.mm"
include "ex.mm"
include "ralrimivva.mm"
include "ctop.mm"
include "topontop.mm"
include "ccld.mm"
include "cpr.mm"
include "wss.mm"
include "wal.mm"
include "cdif.mm"
include "cldopn.mm"
include "adantl.mm"
include "df-3an.mm"
include "ineq2.mm"
include "disjdif.mm"
include "syl6eq.mm"
include "biantrud.mm"
include "neeq1.mm"
include "anbi2d.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "uneq2.mm"
include "undif2.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "wo.mm"
include "cldss.mm"
include "ssequn1.mm"
include "sylib.mm"
include "ssdif0.mm"
include "idd.mm"
include "jctild.mm"
include "eqss.mm"
include "syl6ibr.mm"
include "syl5bir.mm"
include "embantd.mm"
include "orim2d.mm"
include "impexp.mm"
include "wn.mm"
include "df-ne.mm"
include "id.mm"
include "necon4d.mm"
include "necon3d.mm"
include "impbii.mm"
include "imbi12i.mm"
include "pm4.64.mm"
include "bitri.mm"
include "vex.mm"
include "elpr.mm"
include "3imtr4g.mm"
include "syld.mm"
include "com23.mm"
include "imim2d.mm"
include "elin.mm"
include "imbi1i.mm"
include "alimdv.mm"
include "df-ral.mm"
include "dfss2.mm"
include "isconn2.mm"
include "baib.mm"
include "sylibrd.mm"
include "impbid2.mm"
include "toponuni.mm"
include "neeq2d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "bitr4d.mm"

theorem dfconn2
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let cX: class X

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  assert |- ( J e. ( TopOn ` X ) -> ( J e. Conn <-> A. x e. J A. y e. J ( ( x =/= (/) /\ y =/= (/) /\ ( x i^i y ) = (/) ) -> ( x u. y ) =/= X ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    cconn
    wcel
    #
    vx
    cv
    #
    c0
    wne
    #
    vy
    cv
    #
    c0
    wne
    #
    @2
    @4
    cin
    #
    c0
    wceq
    #
    w3a
    #
    @2
    @4
    cun
    #
    cJ
    cuni
    #
    wne
    #
    wi
    #
    vy
    cJ
    wral
    #
    vx
    cJ
    wral
    #
    @8
    @9
    cX
    wne
    #
    wi
    #
    vy
    cJ
    wral
    vx
    cJ
    wral
    @0
    @1
    @14
    @1
    @12
    vx
    vy
    cJ
    cJ
    @1
    @2
    cJ
    wcel
    #
    @4
    cJ
    wcel
    #
    wa
    #
    wa
    #
    @8
    @11
    @20
    @8
    wa
    @2
    @4
    cJ
    @10
    @10
    eqid
    #
    @1
    @19
    @8
    simpll
    @1
    @17
    @18
    @8
    simplrl
    @20
    @3
    @5
    @7
    simpr1
    @1
    @17
    @18
    @8
    simplrr
    @20
    @3
    @5
    @7
    simpr2
    @20
    @3
    @5
    @7
    simpr3
    conndisj
    ex
    ralrimivva
    @0
    cJ
    ctop
    wcel
    #
    @14
    @1
    wi
    cX
    cJ
    topontop
    @22
    @14
    cJ
    cJ
    ccld
    cfv
    #
    cin
    #
    c0
    @10
    cpr
    #
    wss
    #
    @1
    @22
    @17
    @13
    wi
    #
    vx
    wal
    @2
    @24
    wcel
    #
    @2
    @25
    wcel
    #
    wi
    #
    vx
    wal
    @14
    @26
    @22
    @27
    @30
    vx
    @22
    @27
    @17
    @2
    @23
    wcel
    #
    @29
    wi
    #
    wi
    #
    @30
    @22
    @13
    @32
    @17
    @22
    @31
    @13
    @29
    @22
    @31
    @13
    @29
    wi
    @22
    @31
    wa
    #
    @13
    @3
    @10
    @2
    cdif
    #
    c0
    wne
    #
    wa
    #
    @2
    @10
    cun
    #
    @10
    wne
    #
    wi
    #
    @29
    @34
    @35
    cJ
    wcel
    #
    @13
    @40
    wi
    @31
    @41
    @22
    @2
    cJ
    @10
    @21
    cldopn
    adantl
    @12
    @40
    vy
    @35
    cJ
    @4
    @35
    wceq
    #
    @8
    @37
    @11
    @39
    @8
    @3
    @5
    wa
    #
    @7
    wa
    #
    @42
    @37
    @3
    @5
    @7
    df-3an
    @42
    @43
    @44
    @37
    @42
    @7
    @43
    @42
    @6
    @2
    @35
    cin
    c0
    @4
    @35
    @2
    ineq2
    @2
    @10
    disjdif
    syl6eq
    biantrud
    @42
    @5
    @36
    @3
    @4
    @35
    c0
    neeq1
    anbi2d
    bitr3d
    syl5bb
    @42
    @9
    @38
    @10
    @42
    @9
    @2
    @35
    cun
    @38
    @4
    @35
    @2
    uneq2
    @2
    @10
    undif2
    syl6eq
    neeq1d
    imbi12d
    rspcv
    syl
    @34
    @2
    c0
    wceq
    #
    @38
    @10
    wceq
    #
    @35
    c0
    wceq
    #
    wi
    #
    wo
    #
    @45
    @2
    @10
    wceq
    #
    wo
    @40
    @29
    @34
    @48
    @50
    @45
    @34
    @46
    @47
    @50
    @34
    @2
    @10
    wss
    #
    @46
    @31
    @51
    @22
    @2
    cJ
    @10
    @21
    cldss
    adantl
    #
    @2
    @10
    ssequn1
    sylib
    @47
    @10
    @2
    wss
    #
    @34
    @50
    @10
    @2
    ssdif0
    @34
    @53
    @51
    @53
    wa
    @50
    @34
    @53
    @53
    @51
    @34
    @53
    idd
    @52
    jctild
    @2
    @10
    eqss
    syl6ibr
    syl5bir
    embantd
    orim2d
    @40
    @3
    @36
    @39
    wi
    #
    wi
    #
    @49
    @3
    @36
    @39
    impexp
    @55
    @45
    wn
    #
    @48
    wi
    @49
    @3
    @56
    @54
    @48
    @2
    c0
    df-ne
    @54
    @48
    @54
    @35
    c0
    @38
    @10
    @54
    id
    necon4d
    @48
    @38
    @10
    @35
    c0
    @48
    id
    necon3d
    impbii
    imbi12i
    @45
    @48
    pm4.64
    bitri
    bitri
    @2
    c0
    @10
    vx
    vex
    elpr
    3imtr4g
    syld
    ex
    com23
    imim2d
    @30
    @17
    @31
    wa
    #
    @29
    wi
    @33
    @28
    @57
    @29
    @2
    cJ
    @23
    elin
    imbi1i
    @17
    @31
    @29
    impexp
    bitri
    syl6ibr
    alimdv
    @13
    vx
    cJ
    df-ral
    vx
    @24
    @25
    dfss2
    3imtr4g
    @1
    @22
    @26
    cJ
    @10
    @21
    isconn2
    baib
    sylibrd
    syl
    impbid2
    @0
    @16
    @12
    vx
    vy
    cJ
    cJ
    @0
    @15
    @11
    @8
    @0
    cX
    @10
    @9
    cX
    cJ
    toponuni
    neeq2d
    imbi2d
    2ralbidv
    bitr4d
end
