include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cflim.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "cfcls.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "flimfcls.mm"
include "ctopon.mm"
include "ctop.mm"
include "flimtop.mm"
include "toptopon.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "flimss2.mm"
include "syl3anc.mm"
include "simpll.mm"
include "sseldd.mm"
include "sseldi.mm"
include "ex.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "sseq2.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ssid.mm"
include "id.mm"
include "mpi.mm"
include "fclstop.mm"
include "fclselbas.mm"
include "jca.mm"
include "syl.mm"
include "syl6.mm"
include "wn.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "cpw.mm"
include "crab.mm"
include "cun.mm"
include "cfi.mm"
include "cfg.mm"
include "wne.mm"
include "cvv.mm"
include "simplrl.mm"
include "topopn.mm"
include "pwexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "unexg.mm"
include "syl2anc.mm"
include "ssfii.mm"
include "cfbas.mm"
include "filsspw.mm"
include "ssrab2.mm"
include "a1i.mm"
include "unssd.mm"
include "ssun2.mm"
include "difss.mm"
include "wb.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "simprbi.mm"
include "ad2antll.mm"
include "sslin.mm"
include "simprrr.mm"
include "adantr.mm"
include "inssdif0.mm"
include "simplll.mm"
include "simprl.mm"
include "filelss.mm"
include "df-ss.mm"
include "sseq1d.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "ad2antrl.mm"
include "filss.mm"
include "syl13anc.mm"
include "sylbid.mm"
include "syl5bir.mm"
include "necon3bd.mm"
include "mpd.mm"
include "ssn0.mm"
include "ralrimivva.mm"
include "filfbas.mm"
include "filtop.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "pssdifn0.mm"
include "supfil.mm"
include "fbunfip.mm"
include "mpbird.mm"
include "w3a.mm"
include "fsubbas.mm"
include "mpbir3and.mm"
include "ssfg.mm"
include "sstrd.mm"
include "unssad.mm"
include "fgcl.mm"
include "mpid.mm"
include "simprrl.mm"
include "fclsopni.mm"
include "syld.mm"
include "necon2bd.mm"
include "anassrs.mm"
include "expr.mm"
include "con4d.mm"
include "com23.mm"
include "ralrimdva.mm"
include "simprr.mm"
include "jctild.mm"
include "simpl.mm"
include "flimopn.mm"
include "sylibrd.mm"
include "mpdd.mm"
include "impbid2.mm"

theorem flimfnfcls
  let cA: class A
  let vg: setvar g
  let cF: class F
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume flimfnfcls.x: |- X = U. J

  disjoint A g
  disjoint F g
  disjoint J g
  disjoint X g
  disjoint g o
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F o
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint J o
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X o
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( F e. ( Fil ` X ) -> ( A e. ( J fLim F ) <-> A. g e. ( Fil ` X ) ( F C_ g -> A e. ( J fClus g ) ) ) )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cA
    cJ
    cF
    cflim
    co
    #
    wcel
    #
    cF
    vg
    cv
    #
    wss
    #
    cA
    cJ
    @4
    cfcls
    co
    #
    wcel
    #
    wi
    #
    vg
    @0
    wral
    #
    @3
    @8
    vg
    @0
    @3
    @4
    @0
    wcel
    #
    wa
    #
    @5
    @7
    @11
    @5
    wa
    #
    cJ
    @4
    cflim
    co
    #
    @6
    cA
    @4
    cJ
    flimfcls
    @12
    @2
    @13
    cA
    @12
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @10
    @5
    @2
    @13
    wss
    @3
    @14
    @10
    @5
    @3
    cJ
    ctop
    wcel
    #
    @14
    cA
    cF
    cJ
    flimtop
    cJ
    cX
    flimfnfcls.x
    toptopon
    #
    sylib
    ad2antrr
    @3
    @10
    @5
    simplr
    @11
    @5
    simpr
    @4
    cF
    cJ
    cX
    flimss2
    syl3anc
    @3
    @10
    @5
    simpll
    sseldd
    sseldi
    ex
    ralrimiva
    @1
    @9
    @15
    cA
    cX
    wcel
    #
    wa
    #
    @3
    @1
    @9
    cF
    cF
    wss
    #
    cA
    cJ
    cF
    cfcls
    co
    #
    wcel
    #
    wi
    #
    @18
    @8
    @22
    vg
    cF
    @0
    @4
    cF
    wceq
    #
    @5
    @19
    @7
    @21
    @4
    cF
    cF
    sseq2
    @23
    @6
    @20
    cA
    @4
    cF
    cJ
    cfcls
    oveq2
    eleq2d
    imbi12d
    rspcv
    @22
    @21
    @18
    @22
    @19
    @21
    cF
    ssid
    @22
    id
    mpi
    @21
    @15
    @17
    cA
    cF
    cJ
    fclstop
    cA
    cF
    cJ
    cX
    flimfnfcls.x
    fclselbas
    jca
    syl
    syl6
    @1
    @18
    @9
    @3
    @1
    @18
    @9
    @3
    wi
    @1
    @18
    wa
    #
    @9
    @17
    cA
    vo
    cv
    #
    wcel
    #
    @25
    cF
    wcel
    #
    wi
    #
    vo
    cJ
    wral
    #
    wa
    #
    @3
    @24
    @9
    @29
    @17
    @24
    @9
    @28
    vo
    cJ
    @24
    @25
    cJ
    wcel
    #
    wa
    #
    @26
    @9
    @27
    @32
    @26
    @9
    @27
    wi
    @32
    @26
    wa
    @27
    @9
    @32
    @26
    @27
    wn
    #
    @9
    wn
    #
    @24
    @31
    @26
    @33
    wa
    #
    @34
    @24
    @31
    @35
    wa
    #
    wa
    #
    @25
    cX
    @25
    cdif
    #
    cin
    #
    c0
    wceq
    @34
    @25
    cX
    disjdif
    @37
    @9
    @39
    c0
    @37
    @9
    cA
    cJ
    cX
    cF
    @38
    vx
    cv
    #
    wss
    #
    vx
    cX
    cpw
    #
    crab
    #
    cun
    #
    cfi
    cfv
    #
    cfg
    co
    #
    cfcls
    co
    #
    wcel
    #
    @39
    c0
    wne
    #
    @37
    @9
    cF
    @46
    wss
    #
    @48
    @37
    cF
    @43
    @46
    @37
    @44
    @45
    @46
    @37
    @44
    cvv
    wcel
    #
    @44
    @45
    wss
    @37
    @1
    @43
    cvv
    wcel
    #
    @51
    @1
    @18
    @36
    simpll
    #
    @37
    cX
    cJ
    wcel
    #
    @42
    cvv
    wcel
    @52
    @37
    @15
    @54
    @1
    @15
    @17
    @36
    simplrl
    cJ
    cX
    flimfnfcls.x
    topopn
    syl
    #
    cX
    cJ
    pwexg
    @41
    vx
    @42
    cvv
    rabexg
    3syl
    cF
    @43
    @0
    cvv
    unexg
    syl2anc
    @44
    cvv
    ssfii
    syl
    @37
    @45
    cX
    cfbas
    cfv
    #
    wcel
    #
    @45
    @46
    wss
    @37
    @57
    @44
    @42
    wss
    #
    @44
    c0
    wne
    #
    c0
    @45
    wcel
    wn
    #
    @1
    @58
    @18
    @36
    @1
    cF
    @43
    @42
    cF
    cX
    filsspw
    @43
    @42
    wss
    @1
    @41
    vx
    @42
    ssrab2
    a1i
    unssd
    ad2antrr
    @37
    @38
    @44
    wcel
    @59
    @37
    @43
    @44
    @38
    @43
    cF
    ssun2
    @37
    @38
    @42
    wcel
    #
    @38
    @38
    wss
    #
    @38
    @43
    wcel
    @37
    @61
    @38
    cX
    wss
    #
    cX
    @25
    difss
    #
    @37
    @54
    @61
    @63
    wb
    @55
    @38
    cX
    cJ
    elpw2g
    syl
    mpbiri
    @62
    @37
    @38
    ssid
    a1i
    @41
    @62
    vx
    @38
    @42
    @40
    @38
    @38
    sseq2
    elrab
    sylanbrc
    sseldi
    #
    @44
    @38
    ne0i
    syl
    @37
    @60
    vy
    cv
    #
    vz
    cv
    #
    cin
    #
    c0
    wne
    #
    vz
    @43
    wral
    vy
    cF
    wral
    #
    @37
    @69
    vy
    vz
    cF
    @43
    @37
    @66
    cF
    wcel
    #
    @67
    @43
    wcel
    #
    wa
    #
    wa
    #
    @66
    @38
    cin
    #
    @68
    wss
    #
    @75
    c0
    wne
    #
    @69
    @74
    @38
    @67
    wss
    #
    @76
    @72
    @78
    @37
    @71
    @72
    @67
    @42
    wcel
    @78
    @41
    @78
    vx
    @67
    @42
    @40
    @67
    @38
    sseq2
    elrab
    simprbi
    ad2antll
    @38
    @67
    @66
    sslin
    syl
    @74
    @33
    @77
    @37
    @33
    @73
    @24
    @31
    @26
    @33
    simprrr
    #
    adantr
    @74
    @27
    @75
    c0
    @75
    c0
    wceq
    @66
    cX
    cin
    #
    @25
    wss
    #
    @74
    @27
    @66
    cX
    @25
    inssdif0
    @74
    @81
    @66
    @25
    wss
    #
    @27
    @74
    @80
    @66
    @25
    @74
    @66
    cX
    wss
    #
    @80
    @66
    wceq
    @74
    @1
    @71
    @83
    @1
    @18
    @36
    @73
    simplll
    @37
    @71
    @72
    simprl
    @66
    cF
    cX
    filelss
    syl2anc
    @66
    cX
    df-ss
    sylib
    sseq1d
    @74
    @82
    @27
    @74
    @82
    wa
    @1
    @71
    @25
    cX
    wss
    #
    @82
    @27
    @37
    @1
    @73
    @82
    @53
    ad2antrr
    @37
    @71
    @72
    @82
    simplrl
    @37
    @84
    @73
    @82
    @31
    @84
    @24
    @35
    @31
    @25
    cJ
    cuni
    cX
    @25
    cJ
    elssuni
    flimfnfcls.x
    syl6sseqr
    ad2antrl
    #
    ad2antrr
    @74
    @82
    simpr
    @66
    @25
    cF
    cX
    filss
    syl13anc
    ex
    sylbid
    syl5bir
    necon3bd
    mpd
    @75
    @68
    ssn0
    syl2anc
    ralrimivva
    @37
    cF
    @56
    wcel
    #
    @43
    @56
    wcel
    #
    @60
    @70
    wb
    @37
    @1
    @86
    @53
    cF
    cX
    filfbas
    syl
    @37
    @43
    @0
    wcel
    #
    @87
    @37
    @54
    @63
    @38
    c0
    wne
    #
    @88
    @55
    @63
    @37
    @64
    a1i
    @37
    @84
    @25
    cX
    wne
    #
    @89
    @85
    @37
    @33
    @90
    @79
    @37
    @27
    @25
    cX
    @37
    @27
    @25
    cX
    wceq
    cX
    cF
    wcel
    #
    @37
    @1
    @91
    @53
    cF
    cX
    filtop
    syl
    #
    @25
    cX
    cF
    eleq1
    syl5ibrcom
    necon3bd
    mpd
    @25
    cX
    pssdifn0
    syl2anc
    vx
    cX
    @38
    cJ
    supfil
    syl3anc
    @43
    cX
    filfbas
    syl
    vy
    vz
    cF
    @43
    cX
    cX
    fbunfip
    syl2anc
    mpbird
    @37
    @91
    @57
    @58
    @59
    @60
    w3a
    wb
    @92
    @44
    cF
    cX
    fsubbas
    syl
    mpbir3and
    #
    @45
    cX
    ssfg
    syl
    sstrd
    #
    unssad
    @37
    @46
    @0
    wcel
    #
    @9
    @50
    @48
    wi
    #
    wi
    @37
    @57
    @95
    @93
    @45
    cX
    fgcl
    syl
    @8
    @96
    vg
    @46
    @0
    @4
    @46
    wceq
    #
    @5
    @50
    @7
    @48
    @4
    @46
    cF
    sseq2
    @97
    @6
    @47
    cA
    @4
    @46
    cJ
    cfcls
    oveq2
    eleq2d
    imbi12d
    rspcv
    syl
    mpid
    @37
    @48
    @49
    @37
    @48
    wa
    @48
    @31
    @26
    @38
    @46
    wcel
    #
    @49
    @37
    @48
    simpr
    @24
    @31
    @35
    @48
    simplrl
    @37
    @26
    @48
    @24
    @31
    @26
    @33
    simprrl
    adantr
    @37
    @98
    @48
    @37
    @44
    @46
    @38
    @94
    @65
    sseldd
    adantr
    cA
    @38
    @25
    @46
    cJ
    fclsopni
    syl13anc
    ex
    syld
    necon2bd
    mpi
    anassrs
    expr
    con4d
    ex
    com23
    ralrimdva
    @1
    @15
    @17
    simprr
    jctild
    @24
    @14
    @1
    @3
    @30
    wb
    @24
    @15
    @14
    @1
    @15
    @17
    simprl
    @16
    sylib
    @1
    @18
    simpl
    vo
    cA
    cF
    cJ
    cX
    flimopn
    syl2anc
    sylibrd
    ex
    com23
    mpdd
    impbid2
end
