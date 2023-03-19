include "cfn.mm"
include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "wn.mm"
include "cpw.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "wrex.mm"
include "cab.mm"
include "wss.mm"
include "nfv.mm"
include "nfab1.mm"
include "nfcv.mm"
include "wex.mm"
include "wa.mm"
include "abid.mm"
include "df-rex.mm"
include "bitri.mm"
include "eqid.mm"
include "w3a.mm"
include "wsbc.mm"
include "wi.mm"
include "cvv.mm"
include "snex.mm"
include "cdif.mm"
include "c0.mm"
include "wo.mm"
include "snelpwi.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "imdistani.mm"
include "anim2i.mm"
include "3impb.mm"
include "3anass.mm"
include "sylibr.mm"
include "snfi.mm"
include "mpbiri.mm"
include "difinf.mm"
include "sylan2.mm"
include "orcd.mm"
include "ancoms.mm"
include "3impa.mm"
include "syl.mm"
include "rabeq2i.mm"
include "wb.mm"
include "3ad2ant2.mm"
include "mpbid.mm"
include "sbcth.mm"
include "ax-mp.mm"
include "sbcimg.mm"
include "mpbi.mm"
include "sbc3an.mm"
include "sbcg.mm"
include "3anbi1i.mm"
include "eqsbc3.mm"
include "3anbi2i.mm"
include "3bitri.mm"
include "3anbi3i.mm"
include "3imtr3i.mm"
include "mp3an2.mm"
include "ex.mm"
include "pm4.71d.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "syl5bb.mm"
include "anass.mm"
include "exbii.mm"
include "exsimpr.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "ancom.mm"
include "pm5.32i.mm"
include "bitr4i.mm"
include "syl6ib.mm"
include "syl6.mm"
include "ax5e.mm"
include "ssrd.mm"
include "dissneq.mm"
include "sylan.mm"
include "nfielex.mm"
include "adantr.mm"
include "difss.mm"
include "elfvex.mm"
include "difexg.mm"
include "elpwg.mm"
include "3syl.mm"
include "adantl.mm"
include "mpan2.mm"
include "0fin.mm"
include "nsyl.mm"
include "ad2antrl.mm"
include "wne.mm"
include "cin.mm"
include "wpss.mm"
include "vsnid.mm"
include "inelcm.mm"
include "disj4.mm"
include "necon2abii.mm"
include "pssned.mm"
include "neneqd.mm"
include "jca.mm"
include "pm4.56.mm"
include "sylib.mm"
include "biantrurd.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "notbid.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "elrab2.mm"
include "syl6rbbr.mm"
include "dfin4.mm"
include "inss2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "biortn.mm"
include "syl6bbr.mm"
include "ad2antll.mm"
include "mtbird.mm"
include "expcom.mm"
include "nelneq2.mm"
include "eqcom.mm"
include "sylnibr.mm"
include "syl6an.mm"
include "exellimddv.mm"
include "pm2.65da.mm"
include "con4i.mm"

theorem topdifinffinlem
  let vx: setvar x
  let cA: class A
  let cT: class T
  let vu: setvar u
  let vy: setvar y
  assume topdifinf.t: |- T = { x e. ~P A | ( -. ( A \ x ) e. Fin \/ ( x = (/) \/ x = A ) ) }

  disjoint A x
  disjoint T x
  disjoint A x
  disjoint A u
  disjoint A y
  disjoint u y
  disjoint x y
  disjoint T u
  disjoint T y
  assert |- ( T e. ( TopOn ` A ) -> A e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cT
    cA
    ctopon
    cfv
    wcel
    #
    @0
    wn
    #
    @1
    cT
    cA
    cpw
    #
    wceq
    #
    @2
    vu
    cv
    #
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    cA
    wrex
    #
    vu
    cab
    #
    cT
    wss
    @1
    @4
    @2
    vu
    @10
    cT
    @2
    vu
    nfv
    @9
    vu
    nfab1
    vu
    cT
    nfcv
    @2
    @5
    @10
    wcel
    #
    @5
    cT
    wcel
    #
    vy
    wex
    #
    @12
    @2
    @11
    @8
    @12
    wa
    #
    vy
    wex
    #
    @13
    @2
    @11
    @7
    cT
    wcel
    #
    @8
    wa
    #
    vy
    wex
    #
    @15
    @2
    @11
    @6
    cA
    wcel
    #
    @16
    wa
    #
    @8
    wa
    #
    vy
    wex
    #
    @18
    @11
    @19
    @8
    wa
    #
    vy
    wex
    #
    @2
    @22
    @11
    @9
    @24
    @9
    vu
    abid
    @8
    vy
    cA
    df-rex
    bitri
    @2
    @23
    @21
    vy
    @2
    @19
    @20
    @8
    @2
    @19
    @16
    @2
    @19
    @16
    @2
    @7
    @7
    wceq
    #
    @19
    @16
    @7
    eqid
    @2
    vx
    cv
    #
    @7
    wceq
    #
    @19
    w3a
    #
    vx
    @7
    wsbc
    #
    @16
    vx
    @7
    wsbc
    #
    @2
    @25
    @19
    w3a
    #
    @16
    @28
    @16
    wi
    #
    vx
    @7
    wsbc
    #
    @29
    @30
    wi
    #
    @7
    cvv
    wcel
    #
    @33
    @6
    snex
    #
    @32
    vx
    @7
    cvv
    @28
    @26
    cT
    wcel
    #
    @16
    @28
    @26
    @3
    wcel
    #
    cA
    @26
    cdif
    #
    cfn
    wcel
    #
    wn
    #
    @26
    c0
    wceq
    #
    @26
    cA
    wceq
    #
    wo
    #
    wo
    #
    wa
    #
    @37
    @28
    @2
    @27
    @38
    w3a
    #
    @46
    @28
    @2
    @27
    @38
    wa
    #
    wa
    #
    @47
    @2
    @27
    @19
    @49
    @27
    @19
    wa
    @48
    @2
    @27
    @19
    @38
    @19
    @38
    @27
    @7
    @3
    wcel
    @6
    cA
    snelpwi
    @26
    @7
    @3
    eleq1
    syl5ibr
    imdistani
    anim2i
    3impb
    @2
    @27
    @38
    3anass
    sylibr
    @2
    @27
    @38
    @46
    @38
    @2
    @27
    wa
    #
    @46
    @50
    @45
    @38
    @50
    @41
    @44
    @27
    @2
    @26
    cfn
    wcel
    #
    @41
    @27
    @51
    @7
    cfn
    wcel
    #
    @6
    snfi
    #
    @26
    @7
    cfn
    eleq1
    mpbiri
    cA
    @26
    difinf
    sylan2
    orcd
    anim2i
    ancoms
    3impa
    syl
    @45
    vx
    cT
    @3
    topdifinf.t
    rabeq2i
    sylibr
    @27
    @2
    @37
    @16
    wb
    @19
    @26
    @7
    cT
    eleq1
    3ad2ant2
    mpbid
    sbcth
    ax-mp
    @35
    @33
    @34
    wb
    @36
    @28
    @16
    vx
    @7
    cvv
    sbcimg
    ax-mp
    mpbi
    @29
    @2
    @25
    @19
    vx
    @7
    wsbc
    #
    w3a
    #
    @31
    @29
    @2
    vx
    @7
    wsbc
    #
    @27
    vx
    @7
    wsbc
    #
    @54
    w3a
    @2
    @57
    @54
    w3a
    @55
    @2
    @27
    @19
    vx
    @7
    sbc3an
    @56
    @2
    @57
    @54
    @35
    @56
    @2
    wb
    @36
    @2
    vx
    @7
    cvv
    sbcg
    ax-mp
    3anbi1i
    @57
    @25
    @2
    @54
    @35
    @57
    @25
    wb
    @36
    vx
    @7
    @7
    cvv
    eqsbc3
    ax-mp
    3anbi2i
    3bitri
    @54
    @19
    @2
    @25
    @35
    @54
    @19
    wb
    @36
    @19
    vx
    @7
    cvv
    sbcg
    ax-mp
    3anbi3i
    bitri
    @35
    @30
    @16
    wb
    @36
    @16
    vx
    @7
    cvv
    sbcg
    ax-mp
    3imtr3i
    mp3an2
    ex
    pm4.71d
    anbi1d
    exbidv
    syl5bb
    @22
    @19
    @17
    wa
    #
    vy
    wex
    @18
    @21
    @58
    vy
    @19
    @16
    @8
    anass
    exbii
    @19
    @17
    vy
    exsimpr
    sylbi
    syl6bi
    @17
    @14
    vy
    @17
    @8
    @16
    wa
    @14
    @16
    @8
    ancom
    @8
    @12
    @16
    @5
    @7
    cT
    eleq1
    pm5.32i
    bitr4i
    exbii
    syl6ib
    @8
    @12
    vy
    exsimpr
    syl6
    @12
    vy
    ax5e
    syl6
    ssrd
    vy
    vu
    cA
    cT
    @10
    @10
    eqid
    dissneq
    sylan
    @2
    @1
    wa
    #
    @4
    wn
    #
    vy
    cA
    @2
    @19
    vy
    wex
    @1
    vy
    cA
    nfielex
    adantr
    @59
    cA
    @7
    cdif
    #
    @3
    wcel
    #
    @19
    @61
    cT
    wcel
    #
    wn
    #
    @60
    @1
    @62
    @2
    @1
    @62
    @61
    cA
    wss
    #
    cA
    @7
    difss
    @1
    cA
    cvv
    wcel
    @61
    cvv
    wcel
    @62
    @65
    wb
    cT
    cA
    ctopon
    elfvex
    cA
    @7
    cvv
    difexg
    @61
    cA
    cvv
    elpwg
    3syl
    mpbiri
    #
    adantl
    @19
    @59
    @64
    @19
    @59
    wa
    #
    @63
    @61
    c0
    wceq
    #
    @61
    cA
    wceq
    #
    wo
    #
    @67
    @68
    wn
    #
    @69
    wn
    #
    wa
    @70
    wn
    @67
    @71
    @72
    @2
    @71
    @19
    @1
    @2
    @61
    cfn
    wcel
    #
    @68
    @2
    @52
    @73
    wn
    @53
    cA
    @7
    difinf
    mpan2
    @68
    @73
    c0
    cfn
    wcel
    0fin
    @61
    c0
    cfn
    eleq1
    mpbiri
    nsyl
    ad2antrl
    @67
    @61
    cA
    @19
    @61
    cA
    wne
    @59
    @19
    @61
    cA
    @19
    cA
    @7
    cin
    #
    c0
    wne
    #
    @61
    cA
    wpss
    #
    @19
    @6
    @7
    wcel
    @75
    vy
    vsnid
    @6
    cA
    @7
    inelcm
    mpan2
    @76
    @74
    c0
    cA
    @7
    disj4
    necon2abii
    sylibr
    pssned
    adantr
    neneqd
    jca
    @68
    @69
    pm4.56
    sylib
    @1
    @63
    @70
    wb
    @19
    @2
    @1
    @63
    cA
    @61
    cdif
    #
    cfn
    wcel
    #
    wn
    #
    @70
    wo
    #
    @70
    @1
    @80
    @62
    @80
    wa
    @63
    @1
    @62
    @80
    @66
    biantrurd
    @45
    @80
    vx
    @61
    @3
    cT
    @26
    @61
    wceq
    #
    @41
    @79
    @44
    @70
    @81
    @40
    @78
    @81
    @39
    @77
    cfn
    @26
    @61
    cA
    difeq2
    eleq1d
    notbid
    @81
    @42
    @68
    @43
    @69
    @26
    @61
    c0
    eqeq1
    @26
    @61
    cA
    eqeq1
    orbi12d
    orbi12d
    topdifinf.t
    elrab2
    syl6rbbr
    @78
    @70
    @80
    wb
    @74
    @77
    cfn
    cA
    @7
    dfin4
    @52
    @74
    @7
    wss
    @74
    cfn
    wcel
    @53
    cA
    @7
    inss2
    @7
    @74
    ssfi
    mp2an
    eqeltrri
    @78
    @70
    biortn
    ax-mp
    syl6bbr
    ad2antll
    mtbird
    expcom
    @62
    @64
    wa
    @3
    cT
    wceq
    @4
    @61
    @3
    cT
    nelneq2
    cT
    @3
    eqcom
    sylnibr
    syl6an
    exellimddv
    pm2.65da
    con4i
end
