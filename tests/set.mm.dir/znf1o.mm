include "cn0.mm"
include "wcel.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "czrh.mm"
include "cres.mm"
include "cz.mm"
include "wss.mm"
include "ccrg.mm"
include "crg.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "zncrng.mm"
include "crngring.mm"
include "eqid.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "rhmf.mm"
include "4syl.mm"
include "cc0.mm"
include "cfzo.mm"
include "cif.mm"
include "sseq1.mm"
include "ssid.mm"
include "elfzoelz.mm"
include "ssriv.mm"
include "keephyp.mm"
include "eqsstri.mm"
include "fssres.mm"
include "sylancl.mm"
include "feq1i.mm"
include "sylibr.mm"
include "wa.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "fveq1i.mm"
include "fvres.mm"
include "ad2antrl.mm"
include "syl5eq.mm"
include "ad2antll.mm"
include "eqeq12d.mm"
include "wb.mm"
include "simpl.mm"
include "simprl.mm"
include "sseldi.mm"
include "simprr.mm"
include "zndvds.mm"
include "syl3anc.mm"
include "cn.mm"
include "wo.mm"
include "elnn0.mm"
include "cmo.mm"
include "moddvds.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "clt.mm"
include "zred.mm"
include "nnrp.mm"
include "adantr.mm"
include "wne.mm"
include "nnne0.mm"
include "ifnefalse.mm"
include "syl.mm"
include "eleqtrd.mm"
include "elfzole1.mm"
include "elfzolt2.mm"
include "modid.mm"
include "syl22anc.mm"
include "bitr3d.mm"
include "breq1d.mm"
include "id.mm"
include "0nn0.mm"
include "syl6eqel.mm"
include "sylan.mm"
include "zsubcld.mm"
include "0dvds.mm"
include "zcnd.mm"
include "subeq0ad.mm"
include "3bitrd.mm"
include "jaoian.mm"
include "sylanb.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "wrex.mm"
include "crn.mm"
include "zmodfzo.mm"
include "ancoms.mm"
include "eleqtrrd.mm"
include "zre.mm"
include "modabs2.mm"
include "syl2anr.mm"
include "simpr.mm"
include "mpbid.mm"
include "nnnn0.mm"
include "mpbird.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "iftrue.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "syl6eleqr.mm"
include "eqidd.mm"
include "rexbiia.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "znzrhfo.mm"
include "fofn.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "ralrn.mm"
include "3syl.mm"
include "forn.mm"
include "raleqdv.mm"
include "dffo3.mm"
include "df-f1o.mm"

theorem znf1o
  let cB: class B
  let cF: class F
  let cN: class N
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume znf1o.y: |- Y = ( Z/nZ ` N )
  assume znf1o.b: |- B = ( Base ` Y )
  assume znf1o.f: |- F = ( ( ZRHom ` Y ) |` W )
  assume znf1o.w: |- W = if ( N = 0 , ZZ , ( 0 ..^ N ) )


  assert |- ( N e. NN0 -> F : W -1-1-onto-> B )

  proof
    cN
    cn0
    wcel
    #
    cW
    cB
    cF
    wf1
    #
    cW
    cB
    cF
    wfo
    #
    cW
    cB
    cF
    wf1o
    @0
    cW
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
    vx
    vy
    weq
    #
    wi
    #
    vy
    cW
    wral
    vx
    cW
    wral
    @1
    @0
    cW
    cB
    cY
    czrh
    cfv
    #
    cW
    cres
    #
    wf
    #
    @3
    @0
    cz
    cB
    @11
    wf
    #
    cW
    cz
    wss
    @13
    @0
    cY
    ccrg
    wcel
    cY
    crg
    wcel
    @11
    zring
    cY
    crh
    co
    wcel
    @14
    cN
    cY
    znf1o.y
    zncrng
    cY
    crngring
    cY
    @11
    @11
    eqid
    #
    zrhrhm
    cz
    cB
    zring
    cY
    @11
    zringbas
    znf1o.b
    rhmf
    4syl
    cW
    cN
    cc0
    wceq
    #
    cz
    cc0
    cN
    cfzo
    co
    #
    cif
    #
    cz
    znf1o.w
    @16
    cz
    cz
    wss
    @17
    cz
    wss
    @18
    cz
    wss
    cz
    @17
    cz
    @18
    cz
    sseq1
    @17
    @18
    cz
    sseq1
    cz
    ssid
    vx
    @17
    cz
    @4
    cc0
    cN
    elfzoelz
    ssriv
    #
    keephyp
    eqsstri
    #
    cz
    cB
    cW
    @11
    fssres
    sylancl
    cW
    cB
    cF
    @12
    znf1o.f
    feq1i
    sylibr
    #
    @0
    @10
    vx
    vy
    cW
    cW
    @0
    @4
    cW
    wcel
    #
    @6
    cW
    wcel
    #
    wa
    #
    wa
    #
    @8
    @9
    @25
    @8
    @4
    @11
    cfv
    #
    @6
    @11
    cfv
    #
    wceq
    #
    cN
    @4
    @6
    cmin
    co
    #
    cdvds
    wbr
    #
    @9
    @25
    @5
    @26
    @7
    @27
    @25
    @5
    @4
    @12
    cfv
    #
    @26
    @4
    cF
    @12
    znf1o.f
    fveq1i
    @22
    @31
    @26
    wceq
    @0
    @23
    @4
    cW
    @11
    fvres
    ad2antrl
    syl5eq
    @25
    @7
    @6
    @12
    cfv
    #
    @27
    @6
    cF
    @12
    znf1o.f
    fveq1i
    #
    @23
    @32
    @27
    wceq
    @0
    @22
    @6
    cW
    @11
    fvres
    #
    ad2antll
    syl5eq
    eqeq12d
    @25
    @0
    @4
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @28
    @30
    wb
    @0
    @24
    simpl
    @25
    cW
    cz
    @4
    @20
    @0
    @22
    @23
    simprl
    sseldi
    #
    @25
    cW
    cz
    @6
    @20
    @0
    @22
    @23
    simprr
    sseldi
    #
    @4
    @6
    @11
    cN
    cY
    znf1o.y
    @15
    zndvds
    syl3anc
    @0
    cN
    cn
    wcel
    #
    @16
    wo
    #
    @24
    @30
    @9
    wb
    #
    cN
    elnn0
    #
    @39
    @24
    @41
    @16
    @39
    @24
    wa
    #
    @4
    cN
    cmo
    co
    #
    @6
    cN
    cmo
    co
    #
    wceq
    #
    @30
    @9
    @43
    @39
    @35
    @36
    @46
    @30
    wb
    @39
    @24
    simpl
    @43
    cW
    cz
    @4
    @20
    @39
    @22
    @23
    simprl
    #
    sseldi
    #
    @43
    cW
    cz
    @6
    @20
    @39
    @22
    @23
    simprr
    #
    sseldi
    #
    @4
    @6
    cN
    moddvds
    syl3anc
    @43
    @44
    @4
    @45
    @6
    @43
    @4
    cr
    wcel
    cN
    crp
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    @4
    cN
    clt
    wbr
    #
    @44
    @4
    wceq
    @43
    @4
    @48
    zred
    @39
    @51
    @24
    cN
    nnrp
    #
    adantr
    #
    @43
    @4
    @17
    wcel
    #
    @52
    @43
    @4
    cW
    @17
    @47
    @39
    cW
    @17
    wceq
    #
    @24
    @39
    cW
    @18
    @17
    znf1o.w
    @39
    cN
    cc0
    wne
    @18
    @17
    wceq
    cN
    nnne0
    cN
    cc0
    cz
    @17
    ifnefalse
    syl
    syl5eq
    #
    adantr
    #
    eleqtrd
    #
    @4
    cc0
    cN
    elfzole1
    syl
    @43
    @56
    @53
    @60
    @4
    cc0
    cN
    elfzolt2
    syl
    @4
    cN
    modid
    syl22anc
    @43
    @6
    cr
    wcel
    @51
    cc0
    @6
    cle
    wbr
    #
    @6
    cN
    clt
    wbr
    #
    @45
    @6
    wceq
    @43
    @6
    @50
    zred
    @55
    @43
    @6
    @17
    wcel
    #
    @61
    @43
    @6
    cW
    @17
    @49
    @59
    eleqtrd
    #
    @6
    cc0
    cN
    elfzole1
    syl
    @43
    @63
    @62
    @64
    @6
    cc0
    cN
    elfzolt2
    syl
    @6
    cN
    modid
    syl22anc
    eqeq12d
    bitr3d
    @16
    @24
    wa
    #
    @30
    cc0
    @29
    cdvds
    wbr
    #
    @29
    cc0
    wceq
    #
    @9
    @65
    cN
    cc0
    @29
    cdvds
    @16
    @24
    simpl
    breq1d
    @65
    @29
    cz
    wcel
    @66
    @67
    wb
    @65
    @4
    @6
    @16
    @0
    @24
    @35
    @16
    cN
    cc0
    cn0
    @16
    id
    0nn0
    syl6eqel
    #
    @37
    sylan
    #
    @16
    @0
    @24
    @36
    @68
    @38
    sylan
    #
    zsubcld
    @29
    0dvds
    syl
    @65
    @4
    @6
    @65
    @4
    @69
    zcnd
    @65
    @6
    @70
    zcnd
    subeq0ad
    3bitrd
    jaoian
    sylanb
    3bitrd
    biimpd
    ralrimivva
    vx
    vy
    cW
    cB
    cF
    dff13
    sylanbrc
    @0
    @3
    @4
    @7
    wceq
    #
    vy
    cW
    wrex
    #
    vx
    cB
    wral
    #
    @2
    @21
    @0
    @72
    vx
    @11
    crn
    #
    wral
    #
    @73
    @0
    @75
    vz
    cv
    #
    @11
    cfv
    #
    @7
    wceq
    #
    vy
    cW
    wrex
    #
    vz
    cz
    wral
    #
    @0
    @79
    vz
    cz
    @0
    @76
    cz
    wcel
    #
    wa
    @77
    @27
    wceq
    #
    vy
    cW
    wrex
    #
    @79
    @0
    @40
    @81
    @83
    @42
    @39
    @81
    @83
    @16
    @39
    @81
    wa
    #
    @76
    cN
    cmo
    co
    #
    cW
    wcel
    @77
    @85
    @11
    cfv
    #
    wceq
    #
    @83
    @84
    @85
    @17
    cW
    @81
    @39
    @85
    @17
    wcel
    @76
    cN
    zmodfzo
    ancoms
    #
    @39
    @57
    @81
    @58
    adantr
    eleqtrrd
    @84
    @86
    @77
    @84
    @86
    @77
    wceq
    #
    cN
    @85
    @76
    cmin
    co
    cdvds
    wbr
    #
    @84
    @85
    cN
    cmo
    co
    @85
    wceq
    #
    @90
    @81
    @76
    cr
    wcel
    @51
    @91
    @39
    @76
    zre
    @54
    @76
    cN
    modabs2
    syl2anr
    @84
    @39
    @85
    cz
    wcel
    #
    @81
    @91
    @90
    wb
    @39
    @81
    simpl
    @84
    @17
    cz
    @85
    @19
    @88
    sseldi
    #
    @39
    @81
    simpr
    #
    @85
    @76
    cN
    moddvds
    syl3anc
    mpbid
    @84
    @0
    @92
    @81
    @89
    @90
    wb
    @39
    @0
    @81
    cN
    nnnn0
    adantr
    @93
    @94
    @85
    @76
    @11
    cN
    cY
    znf1o.y
    @15
    zndvds
    syl3anc
    mpbird
    eqcomd
    @82
    @87
    vy
    @85
    cW
    @6
    @85
    wceq
    @27
    @86
    @77
    @6
    @85
    @11
    fveq2
    eqeq2d
    rspcev
    syl2anc
    @16
    @81
    wa
    #
    @76
    cW
    wcel
    @77
    @77
    wceq
    #
    @83
    @95
    @76
    @18
    cW
    @16
    @76
    @18
    wcel
    @81
    @16
    @18
    cz
    @76
    @16
    cz
    @17
    iftrue
    eleq2d
    biimpar
    znf1o.w
    syl6eleqr
    @95
    @77
    eqidd
    @82
    @96
    vy
    @76
    cW
    vy
    vz
    weq
    @27
    @77
    @77
    @6
    @76
    @11
    fveq2
    eqeq2d
    rspcev
    syl2anc
    jaoian
    sylanb
    @78
    @82
    vy
    cW
    @23
    @7
    @27
    @77
    @23
    @7
    @32
    @27
    @33
    @34
    syl5eq
    eqeq2d
    rexbiia
    sylibr
    ralrimiva
    @0
    cz
    cB
    @11
    wfo
    #
    @11
    cz
    wfn
    @75
    @80
    wb
    cB
    @11
    cN
    cY
    znf1o.y
    znf1o.b
    @15
    znzrhfo
    #
    cz
    cB
    @11
    fofn
    @72
    @79
    vx
    vz
    cz
    @11
    @4
    @77
    wceq
    @71
    @78
    vy
    cW
    @4
    @77
    @7
    eqeq1
    rexbidv
    ralrn
    3syl
    mpbird
    @0
    @72
    vx
    @74
    cB
    @0
    @97
    @74
    cB
    wceq
    @98
    cz
    cB
    @11
    forn
    syl
    raleqdv
    mpbid
    vy
    vx
    cW
    cB
    cF
    dffo3
    sylanbrc
    cW
    cB
    cF
    df-f1o
    sylanbrc
end
