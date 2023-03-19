include "cicc.mm"
include "co.mm"
include "crn.mm"
include "clt.mm"
include "wiso.mm"
include "ccnv.mm"
include "wo.mm"
include "cr.mm"
include "cdv.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioo.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "crp.mm"
include "wss.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "wn.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "imp.mm"
include "wbr.mm"
include "wb.mm"
include "cdm.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "dvfre.mm"
include "frn.mm"
include "sselda.mm"
include "0re.mm"
include "lttri2.mm"
include "sylancl.mm"
include "cxr.mm"
include "0xr.mm"
include "elioomnf.mm"
include "ax-mp.mm"
include "baib.mm"
include "elrp.mm"
include "orbi12d.mm"
include "bitr4d.mm"
include "mpbid.mm"
include "elun.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "disjssun.mm"
include "syl5ibcom.mm"
include "adantr.mm"
include "wfn.mm"
include "feq2d.mm"
include "ffn.mm"
include "anim1i.mm"
include "df-f.mm"
include "dvgt0.mm"
include "orcd.mm"
include "syldan.mm"
include "wex.mm"
include "n0.mm"
include "elin.mm"
include "cfv.mm"
include "wrex.mm"
include "wi.mm"
include "fvelrnb.mm"
include "wral.mm"
include "ffvelrnda.mm"
include "cle.mm"
include "ad2antrr.mm"
include "cres.mm"
include "simplrl.mm"
include "simprl.mm"
include "ioossicc.mm"
include "rescncf.mm"
include "mpsyl.mm"
include "ctg.mm"
include "cnt.mm"
include "cc.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "fss.mm"
include "syl5ss.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "ctop.mm"
include "retop.mm"
include "iooretop.mm"
include "isopn3i.mm"
include "mp2an.mm"
include "reseq2i.mm"
include "fnresdm.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "dmeqd.mm"
include "dvivth.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "rneqd.mm"
include "3sstr3d.mm"
include "simplrr.mm"
include "sylib.mm"
include "simprd.mm"
include "simpld.mm"
include "ltle.mm"
include "mpd.mm"
include "simprr.mm"
include "w3a.mm"
include "elicc2.mm"
include "mpbir3and.mm"
include "sseldd.mm"
include "expr.mm"
include "mtod.mm"
include "ltnle.mm"
include "mpbird.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "dvlt0.mm"
include "olcd.mm"
include "imbi1d.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "impd.mm"
include "syl5bi.mm"
include "exlimdv.mm"
include "pm2.61dane.mm"

theorem dvne0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dvne0.a: |- ( ph -> A e. RR )
  assume dvne0.b: |- ( ph -> B e. RR )
  assume dvne0.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )
  assume dvne0.d: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume dvne0.z: |- ( ph -> -. 0 e. ran ( RR _D F ) )


  assert |- ( ph -> ( F Isom < , < ( ( A [,] B ) , ran F ) \/ F Isom < , `' < ( ( A [,] B ) , ran F ) ) )

  proof
    wph
    cA
    cB
    cicc
    co
    #
    cF
    crn
    #
    clt
    clt
    cF
    wiso
    #
    @0
    @1
    clt
    clt
    ccnv
    cF
    wiso
    #
    wo
    #
    cr
    cF
    cdv
    co
    #
    crn
    #
    cmnf
    cc0
    cioo
    co
    #
    cin
    #
    c0
    wph
    @8
    c0
    wceq
    #
    @6
    crp
    wss
    #
    @4
    wph
    @9
    @10
    wph
    @6
    @7
    crp
    cun
    #
    wss
    @9
    @10
    wph
    vx
    @6
    @11
    wph
    vx
    cv
    #
    @6
    wcel
    #
    @12
    @11
    wcel
    #
    wph
    @13
    wa
    #
    @12
    @7
    wcel
    #
    @12
    crp
    wcel
    #
    wo
    #
    @14
    @15
    @12
    cc0
    wne
    #
    @18
    wph
    @13
    @19
    wph
    @13
    @12
    cc0
    wph
    @13
    wn
    @12
    cc0
    wceq
    #
    cc0
    @6
    wcel
    #
    wn
    #
    dvne0.z
    @20
    @13
    @21
    @12
    cc0
    @6
    eleq1
    notbid
    syl5ibrcom
    necon2ad
    imp
    @15
    @19
    @12
    cc0
    clt
    wbr
    #
    cc0
    @12
    clt
    wbr
    #
    wo
    #
    @18
    @15
    @12
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @19
    @25
    wb
    wph
    @6
    cr
    @12
    wph
    @5
    cdm
    #
    cr
    @5
    wf
    #
    @6
    cr
    wss
    wph
    @0
    cr
    cF
    wf
    #
    @0
    cr
    wss
    #
    @29
    wph
    cF
    @0
    cr
    ccncf
    co
    wcel
    #
    @30
    dvne0.f
    @0
    cr
    cF
    cncff
    syl
    #
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @31
    dvne0.a
    dvne0.b
    cA
    cB
    iccssre
    syl2anc
    #
    @0
    cF
    dvfre
    syl2anc
    #
    @28
    cr
    @5
    frn
    syl
    sselda
    #
    0re
    @12
    cc0
    lttri2
    sylancl
    @15
    @26
    @18
    @25
    wb
    @38
    @26
    @16
    @23
    @17
    @24
    @16
    @26
    @23
    cc0
    cxr
    wcel
    #
    @16
    @26
    @23
    wa
    wb
    0xr
    cc0
    @12
    elioomnf
    ax-mp
    baib
    @17
    @26
    @24
    @12
    elrp
    baib
    orbi12d
    syl
    bitr4d
    mpbid
    @12
    @7
    crp
    elun
    sylibr
    ex
    ssrdv
    @6
    @7
    crp
    disjssun
    syl5ibcom
    imp
    wph
    @10
    wa
    #
    @2
    @3
    @40
    cA
    cB
    cF
    wph
    @34
    @10
    dvne0.a
    adantr
    wph
    @35
    @10
    dvne0.b
    adantr
    wph
    @32
    @10
    dvne0.f
    adantr
    @40
    @5
    cA
    cB
    cioo
    co
    #
    wfn
    #
    @10
    wa
    @41
    crp
    @5
    wf
    wph
    @42
    @10
    wph
    @41
    cr
    @5
    wf
    #
    @42
    wph
    @29
    @43
    @37
    wph
    @28
    @41
    cr
    @5
    dvne0.d
    feq2d
    mpbid
    #
    @41
    cr
    @5
    ffn
    syl
    #
    anim1i
    @41
    crp
    @5
    df-f
    sylibr
    dvgt0
    orcd
    syldan
    wph
    @8
    c0
    wne
    #
    @4
    @46
    @12
    @8
    wcel
    #
    vx
    wex
    wph
    @4
    vx
    @8
    n0
    wph
    @47
    @4
    vx
    @47
    @13
    @16
    wa
    wph
    @4
    @12
    @6
    @7
    elin
    wph
    @13
    @16
    @4
    wph
    @13
    vy
    cv
    #
    @5
    cfv
    #
    @12
    wceq
    #
    vy
    @41
    wrex
    #
    @16
    @4
    wi
    #
    wph
    @42
    @13
    @51
    wb
    @45
    vy
    @41
    @12
    @5
    fvelrnb
    syl
    wph
    @50
    @52
    vy
    @41
    wph
    @48
    @41
    wcel
    #
    wa
    @49
    @7
    wcel
    #
    @4
    wi
    @50
    @52
    wph
    @53
    @54
    @4
    wph
    @53
    @54
    wa
    #
    wa
    #
    @3
    @2
    @56
    cA
    cB
    cF
    wph
    @34
    @55
    dvne0.a
    adantr
    wph
    @35
    @55
    dvne0.b
    adantr
    wph
    @32
    @55
    dvne0.f
    adantr
    @56
    @42
    vz
    cv
    #
    @5
    cfv
    #
    @7
    wcel
    #
    vz
    @41
    wral
    @41
    @7
    @5
    wf
    wph
    @42
    @55
    @45
    adantr
    @56
    @59
    vz
    @41
    @56
    @57
    @41
    wcel
    #
    wa
    #
    @58
    cr
    wcel
    #
    @58
    cc0
    clt
    wbr
    #
    @59
    @56
    @41
    cr
    @57
    @5
    wph
    @43
    @55
    @44
    adantr
    ffvelrnda
    #
    @61
    @63
    cc0
    @58
    cle
    wbr
    #
    wn
    #
    @61
    @65
    @21
    wph
    @22
    @55
    @60
    dvne0.z
    ad2antrr
    @56
    @60
    @65
    @21
    @56
    @60
    @65
    wa
    #
    wa
    #
    @49
    @58
    cicc
    co
    #
    @6
    cc0
    @68
    @48
    cr
    cF
    @41
    cres
    #
    cdv
    co
    #
    cfv
    #
    @57
    @71
    cfv
    #
    cicc
    co
    @71
    crn
    @69
    @6
    @68
    cA
    cB
    @70
    @48
    @57
    wph
    @53
    @54
    @67
    simplrl
    @56
    @60
    @65
    simprl
    #
    wph
    @70
    @41
    cr
    ccncf
    co
    wcel
    #
    @55
    @67
    @41
    @0
    wss
    wph
    @32
    @75
    cA
    cB
    ioossicc
    #
    dvne0.f
    @0
    cr
    @41
    cF
    rescncf
    mpsyl
    ad2antrr
    wph
    @71
    cdm
    #
    @41
    wceq
    @55
    @67
    wph
    @77
    @28
    @41
    wph
    @71
    @5
    wph
    @71
    @5
    @41
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @5
    wph
    cr
    cc
    wss
    #
    @0
    cc
    cF
    wf
    #
    @31
    @41
    cr
    wss
    @71
    @80
    wceq
    @81
    wph
    ax-resscn
    a1i
    wph
    @30
    @81
    @82
    @33
    ax-resscn
    @0
    cr
    cc
    cF
    fss
    sylancl
    @36
    wph
    @41
    @0
    cr
    @76
    @36
    syl5ss
    @0
    @41
    cr
    @78
    cF
    ccnfld
    ctopn
    cfv
    #
    @83
    eqid
    #
    @83
    @84
    tgioo2
    dvres
    syl22anc
    wph
    @80
    @5
    @41
    cres
    #
    @5
    @79
    @41
    @5
    @78
    ctop
    wcel
    @41
    @78
    wcel
    @79
    @41
    wceq
    retop
    cA
    cB
    iooretop
    @41
    @78
    isopn3i
    mp2an
    reseq2i
    wph
    @42
    @85
    @5
    wceq
    @45
    @41
    @5
    fnresdm
    syl
    syl5eq
    eqtrd
    #
    dmeqd
    dvne0.d
    eqtrd
    ad2antrr
    dvivth
    @68
    @72
    @49
    @73
    @58
    cicc
    @68
    @48
    @71
    @5
    wph
    @71
    @5
    wceq
    @55
    @67
    @86
    ad2antrr
    #
    fveq1d
    @68
    @57
    @71
    @5
    @87
    fveq1d
    oveq12d
    @68
    @71
    @5
    @87
    rneqd
    3sstr3d
    @68
    cc0
    @69
    wcel
    #
    @27
    @49
    cc0
    cle
    wbr
    #
    @65
    @27
    @68
    0re
    a1i
    @68
    @49
    cc0
    clt
    wbr
    #
    @89
    @68
    @49
    cr
    wcel
    #
    @90
    @68
    @54
    @91
    @90
    wa
    #
    wph
    @53
    @54
    @67
    simplrr
    @39
    @54
    @92
    wb
    0xr
    cc0
    @49
    elioomnf
    ax-mp
    sylib
    #
    simprd
    @68
    @91
    @27
    @90
    @89
    wi
    @68
    @91
    @90
    @93
    simpld
    #
    0re
    @49
    cc0
    ltle
    sylancl
    mpd
    @56
    @60
    @65
    simprr
    @68
    @91
    @62
    @88
    @27
    @89
    @65
    w3a
    wb
    @94
    @56
    @67
    @60
    @62
    @74
    @64
    syldan
    @49
    @58
    cc0
    elicc2
    syl2anc
    mpbir3and
    sseldd
    expr
    mtod
    @61
    @62
    @27
    @63
    @66
    wb
    @64
    0re
    @58
    cc0
    ltnle
    sylancl
    mpbird
    @39
    @59
    @62
    @63
    wa
    wb
    0xr
    cc0
    @58
    elioomnf
    ax-mp
    sylanbrc
    ralrimiva
    vz
    @41
    @7
    @5
    ffnfv
    sylanbrc
    dvlt0
    olcd
    expr
    @50
    @54
    @16
    @4
    @49
    @12
    @7
    eleq1
    imbi1d
    syl5ibcom
    rexlimdva
    sylbid
    impd
    syl5bi
    exlimdv
    syl5bi
    imp
    pm2.61dane
end
