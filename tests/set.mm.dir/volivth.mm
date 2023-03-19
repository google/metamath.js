include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wrex.mm"
include "cneg.mm"
include "cin.mm"
include "cn.mm"
include "cr.mm"
include "simpll.mm"
include "cmnf.mm"
include "cxr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "iccssxr.mm"
include "simpr.mm"
include "sseldi.mm"
include "adantr.mm"
include "cpnf.mm"
include "volf.mm"
include "ffvelrni.mm"
include "cle.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "elicc1.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp2d.mm"
include "wi.mm"
include "mnflt0.mm"
include "xrltletr.mm"
include "mpani.mm"
include "mp3an12.mm"
include "sylc.mm"
include "xrre2.mm"
include "syl32anc.mm"
include "volsup2.mm"
include "syl3anc.mm"
include "cmpt.mm"
include "nnre.mm"
include "ad2antrl.mm"
include "renegcld.mm"
include "0red.mm"
include "nngt0.mm"
include "lt0neg2d.mm"
include "lttrd.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ccncf.mm"
include "cc.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "eqid.mm"
include "volcn.mm"
include "sselda.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "covol.mm"
include "oveq2.mm"
include "ineq2d.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "csn.mm"
include "inss2.mm"
include "rexrd.mm"
include "iccid.mm"
include "syl5sseq.mm"
include "snssd.mm"
include "sstrd.mm"
include "ovolsn.mm"
include "ovolssnul.mm"
include "nulmbl.mm"
include "mblvol.mm"
include "3eqtrd.mm"
include "eqbrtrd.mm"
include "simprr.mm"
include "iccmbl.mm"
include "inmbl.mm"
include "xrltle.mm"
include "mpd.mm"
include "breqtrrd.mm"
include "jca.mm"
include "ivthle.mm"
include "eqeq1d.mm"
include "adantrr.mm"
include "inss1.mm"
include "sseq1.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "expr.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "rexlimddv.mm"
include "eqcomd.mm"
include "wo.mm"
include "simp3d.mm"
include "xrleloe.mm"
include "mpjaodan.mm"

theorem volivth
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint n u
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B n
  disjoint B u
  disjoint B z
  assert |- ( ( A e. dom vol /\ B e. ( 0 [,] ( vol ` A ) ) ) -> E. x e. dom vol ( x C_ A /\ ( vol ` x ) = B ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    cc0
    cA
    cvol
    cfv
    #
    cicc
    co
    #
    wcel
    #
    wa
    #
    cB
    @2
    clt
    wbr
    #
    vx
    cv
    #
    cA
    wss
    #
    @7
    cvol
    cfv
    #
    cB
    wceq
    #
    wa
    #
    vx
    @0
    wrex
    #
    cB
    @2
    wceq
    #
    @5
    @6
    wa
    #
    cB
    cA
    vn
    cv
    #
    cneg
    #
    @15
    cicc
    co
    #
    cin
    #
    cvol
    cfv
    #
    clt
    wbr
    #
    @12
    vn
    cn
    @14
    @1
    cB
    cr
    wcel
    #
    @6
    @20
    vn
    cn
    wrex
    @1
    @4
    @6
    simpll
    #
    @14
    cmnf
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    cmnf
    cB
    clt
    wbr
    #
    @6
    @21
    @23
    @14
    mnfxr
    a1i
    @5
    @24
    @6
    @5
    @3
    cxr
    cB
    cc0
    @2
    iccssxr
    @1
    @4
    simpr
    #
    sseldi
    #
    adantr
    #
    @5
    @25
    @6
    @1
    @25
    @4
    @1
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @2
    cc0
    cpnf
    iccssxr
    #
    @0
    @30
    cA
    cvol
    volf
    ffvelrni
    sseldi
    adantr
    #
    adantr
    @14
    @24
    cc0
    cB
    cle
    wbr
    #
    @26
    @29
    @5
    @33
    @6
    @5
    @24
    @33
    cB
    @2
    cle
    wbr
    #
    @5
    @4
    @24
    @33
    @34
    w3a
    #
    @27
    @5
    cc0
    cxr
    wcel
    #
    @25
    @4
    @35
    wb
    0xr
    @32
    cc0
    @2
    cB
    elicc1
    sylancr
    mpbid
    #
    simp2d
    adantr
    #
    @23
    @36
    @24
    @33
    @26
    wi
    mnfxr
    0xr
    @23
    @36
    @24
    w3a
    cmnf
    cc0
    clt
    wbr
    @33
    @26
    mnflt0
    cmnf
    cc0
    cB
    xrltletr
    mpani
    mp3an12
    sylc
    @5
    @6
    simpr
    #
    cmnf
    cB
    @2
    xrre2
    syl32anc
    #
    @39
    cA
    cB
    vn
    volsup2
    syl3anc
    @14
    @15
    cn
    wcel
    #
    @20
    wa
    #
    wa
    #
    vz
    cv
    #
    vy
    cr
    cA
    @16
    vy
    cv
    #
    cicc
    co
    #
    cin
    #
    cvol
    cfv
    #
    cmpt
    #
    cfv
    #
    cB
    wceq
    #
    vz
    @17
    wrex
    @12
    @43
    vu
    @16
    @15
    cr
    cB
    @49
    vz
    @43
    @15
    @41
    @15
    cr
    wcel
    #
    @14
    @20
    @15
    nnre
    ad2antrl
    #
    renegcld
    #
    @53
    @14
    @21
    @42
    @40
    adantr
    @43
    @16
    cc0
    @15
    @54
    @43
    0red
    @53
    @43
    cc0
    @15
    clt
    wbr
    #
    @16
    cc0
    clt
    wbr
    @41
    @55
    @14
    @20
    @15
    nngt0
    ad2antrl
    #
    @43
    @15
    @53
    lt0neg2d
    mpbid
    @56
    lttrd
    @43
    @16
    cr
    wcel
    #
    @52
    @17
    cr
    wss
    @54
    @53
    @16
    @15
    iccssre
    syl2anc
    #
    @43
    cr
    cr
    ccncf
    co
    #
    cr
    cc
    ccncf
    co
    #
    @49
    cr
    cc
    wss
    cc
    cc
    wss
    @59
    @60
    wss
    ax-resscn
    cc
    ssid
    cr
    cr
    cc
    cncfss
    mp2an
    @43
    @1
    @57
    @49
    @59
    wcel
    #
    @14
    @1
    @42
    @22
    adantr
    #
    @54
    vy
    cA
    @16
    @49
    @49
    eqid
    #
    volcn
    syl2anc
    #
    sseldi
    @43
    vu
    cv
    #
    @17
    wcel
    @65
    cr
    wcel
    @65
    @49
    cfv
    cr
    wcel
    @43
    @17
    cr
    @65
    @58
    sselda
    @43
    cr
    cr
    @65
    @49
    @43
    @61
    cr
    cr
    @49
    wf
    @64
    cr
    cr
    @49
    cncff
    syl
    ffvelrnda
    syldan
    @43
    @16
    @49
    cfv
    #
    cB
    cle
    wbr
    cB
    @15
    @49
    cfv
    #
    cle
    wbr
    @43
    @66
    cc0
    cB
    cle
    @43
    @66
    cA
    @16
    @16
    cicc
    co
    #
    cin
    #
    cvol
    cfv
    #
    @69
    covol
    cfv
    #
    cc0
    @43
    @57
    @66
    @70
    wceq
    @54
    vy
    @16
    @48
    @70
    cr
    @49
    @45
    @16
    wceq
    #
    @47
    @69
    cvol
    @72
    @46
    @68
    cA
    @45
    @16
    @16
    cicc
    oveq2
    ineq2d
    fveq2d
    @63
    @69
    cvol
    fvex
    fvmpt
    syl
    @43
    @69
    @0
    wcel
    #
    @70
    @71
    wceq
    @43
    @69
    cr
    wss
    @71
    cc0
    wceq
    #
    @73
    @43
    @69
    @16
    csn
    #
    cr
    @43
    @68
    @69
    @75
    cA
    @68
    inss2
    @43
    @16
    cxr
    wcel
    @68
    @75
    wceq
    @43
    @16
    @54
    rexrd
    @16
    iccid
    syl
    syl5sseq
    #
    @43
    @16
    cr
    @54
    snssd
    #
    sstrd
    @43
    @69
    @75
    wss
    @75
    cr
    wss
    @75
    covol
    cfv
    cc0
    wceq
    #
    @74
    @76
    @77
    @43
    @57
    @78
    @54
    @16
    ovolsn
    syl
    @69
    @75
    ovolssnul
    syl3anc
    #
    @69
    nulmbl
    syl2anc
    @69
    mblvol
    syl
    @79
    3eqtrd
    @14
    @33
    @42
    @38
    adantr
    eqbrtrd
    @43
    cB
    @19
    @67
    cle
    @43
    @20
    cB
    @19
    cle
    wbr
    #
    @14
    @41
    @20
    simprr
    @43
    @24
    @19
    cxr
    wcel
    #
    @20
    @80
    wi
    @14
    @24
    @42
    @29
    adantr
    @43
    @18
    @0
    wcel
    #
    @81
    @43
    @1
    @17
    @0
    wcel
    #
    @82
    @62
    @43
    @57
    @52
    @83
    @54
    @53
    @16
    @15
    iccmbl
    syl2anc
    cA
    @17
    inmbl
    syl2anc
    @82
    @30
    cxr
    @19
    @31
    @0
    @30
    @18
    cvol
    volf
    ffvelrni
    sseldi
    syl
    cB
    @19
    xrltle
    syl2anc
    mpd
    @43
    @52
    @67
    @19
    wceq
    @53
    vy
    @15
    @48
    @19
    cr
    @49
    @45
    @15
    wceq
    #
    @47
    @18
    cvol
    @84
    @46
    @17
    cA
    @45
    @15
    @16
    cicc
    oveq2
    ineq2d
    fveq2d
    @63
    @18
    cvol
    fvex
    fvmpt
    syl
    breqtrrd
    jca
    ivthle
    @43
    @51
    @12
    vz
    @17
    @43
    @44
    @17
    wcel
    #
    wa
    #
    @51
    cA
    @16
    @44
    cicc
    co
    #
    cin
    #
    cvol
    cfv
    #
    cB
    wceq
    #
    @12
    @86
    @50
    @89
    cB
    @86
    @44
    cr
    wcel
    #
    @50
    @89
    wceq
    @43
    @17
    cr
    @44
    @58
    sselda
    #
    vy
    @44
    @48
    @89
    cr
    @49
    @45
    @44
    wceq
    #
    @47
    @88
    cvol
    @93
    @46
    @87
    cA
    @45
    @44
    @16
    cicc
    oveq2
    ineq2d
    fveq2d
    @63
    @88
    cvol
    fvex
    fvmpt
    syl
    eqeq1d
    @43
    @85
    @90
    @12
    @43
    @85
    @90
    wa
    #
    wa
    #
    @88
    @0
    wcel
    #
    @88
    cA
    wss
    #
    @90
    @12
    @95
    @1
    @87
    @0
    wcel
    #
    @96
    @43
    @1
    @94
    @62
    adantr
    @95
    @57
    @91
    @98
    @43
    @57
    @94
    @54
    adantr
    @43
    @85
    @91
    @90
    @92
    adantrr
    @16
    @44
    iccmbl
    syl2anc
    cA
    @87
    inmbl
    syl2anc
    @97
    @95
    cA
    @87
    inss1
    a1i
    @43
    @85
    @90
    simprr
    @11
    @97
    @90
    wa
    vx
    @88
    @0
    @7
    @88
    wceq
    #
    @8
    @97
    @10
    @90
    @7
    @88
    cA
    sseq1
    @99
    @9
    @89
    cB
    @7
    @88
    cvol
    fveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    expr
    sylbid
    rexlimdva
    mpd
    rexlimddv
    @5
    @13
    wa
    #
    @1
    cA
    cA
    wss
    #
    @2
    cB
    wceq
    #
    @12
    @1
    @4
    @13
    simpll
    @101
    @100
    cA
    ssid
    a1i
    @100
    cB
    @2
    @5
    @13
    simpr
    eqcomd
    @11
    @101
    @102
    wa
    vx
    cA
    @0
    @7
    cA
    wceq
    #
    @8
    @101
    @10
    @102
    @7
    cA
    cA
    sseq1
    @103
    @9
    @2
    cB
    @7
    cA
    cvol
    fveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    @5
    @34
    @6
    @13
    wo
    #
    @5
    @24
    @33
    @34
    @37
    simp3d
    @5
    @24
    @25
    @34
    @104
    wb
    @28
    @32
    cB
    @2
    xrleloe
    syl2anc
    mpbid
    mpjaodan
end
