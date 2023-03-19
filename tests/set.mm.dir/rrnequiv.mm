include "wcel.mm"
include "wa.mm"
include "co.mm"
include "crrn.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "chash.mm"
include "csqrt.mm"
include "cmul.mm"
include "cv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "cmpt.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "ccnfld.mm"
include "csca.mm"
include "cress.mm"
include "cprds.mm"
include "cds.mm"
include "cvv.mm"
include "cfn.mm"
include "wceq.mm"
include "ovex.mm"
include "adantr.mm"
include "reex.mm"
include "eqid.mm"
include "resssca.mm"
include "ax-mp.mm"
include "pwsval.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "cbs.mm"
include "fconstmpt.mm"
include "oveq2i.mm"
include "fvexd.mm"
include "a1i.mm"
include "ralrimiva.mm"
include "simprl.mm"
include "cmap.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "cnfldbas.mm"
include "ressbas2.mm"
include "pwsbas.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "simprr.mm"
include "cnfldds.mm"
include "ressds.mm"
include "reseq1i.mm"
include "prdsdsval3.mm"
include "wral.mm"
include "rrndstprj1.mm"
include "an32s.mm"
include "sylanl1.mm"
include "wb.mm"
include "rgenw.mm"
include "breq1.mm"
include "ralrnmpt.mm"
include "sylibr.mm"
include "cme.mm"
include "rrnmet.mm"
include "syl.mm"
include "metge0.mm"
include "syl3anc.mm"
include "elsni.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "ralrimiv.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "wf.mm"
include "prdsbascl.mm"
include "r19.21bi.mm"
include "remet.mm"
include "metcl.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "frn.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "0xr.mm"
include "snssd.mm"
include "unssd.mm"
include "sseldi.mm"
include "supxrleub.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "c0.mm"
include "rzal.mm"
include "wfn.mm"
include "syl6eleq.mm"
include "elmapi.mm"
include "ffn.mm"
include "3syl.mm"
include "eqfnfv.mm"
include "syl5ibr.mm"
include "imp.mm"
include "oveq1d.mm"
include "met0.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "resqrtcld.mm"
include "repwsmet.mm"
include "sqrtge0d.mm"
include "mulge0d.mm"
include "wne.mm"
include "caddc.mm"
include "crp.mm"
include "remulcld.mm"
include "rpre.mm"
include "ad2antll.mm"
include "readdcld.mm"
include "cdiv.mm"
include "cdif.mm"
include "eldifsn.mm"
include "cn.mm"
include "hashnncl.mm"
include "nnrpd.mm"
include "rpsqrtcld.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "0red.mm"
include "ltaddrpd.mm"
include "lelttrd.mm"
include "elrpd.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "ssun1.mm"
include "simpr.mm"
include "elrnmpt1.mm"
include "sylancl.mm"
include "supxrub.mm"
include "breqtrrd.mm"
include "rrndstprj2.mm"
include "syl32anc.mm"
include "recnd.mm"
include "adddird.mm"
include "mulcomd.mm"
include "rpne0d.mm"
include "divcan1d.mm"
include "oveq12d.mm"
include "breqtrd.mm"
include "ltled.mm"
include "anassrs.mm"
include "alrple.mm"
include "pm2.61dane.mm"
include "jca.mm"

theorem rrnequiv
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vr: setvar r
  let vz: setvar z
  assume rrnequiv.y: |- Y = ( ( CCfld |`s RR ) ^s I )
  assume rrnequiv.d: |- D = ( dist ` Y )
  assume rrnequiv.1: |- X = ( RR ^m I )
  assume rrnequiv.i: |- ( ph -> I e. Fin )


  assert |- ( ( ph /\ ( F e. X /\ G e. X ) ) -> ( ( F D G ) <_ ( F ( Rn ` I ) G ) /\ ( F ( Rn ` I ) G ) <_ ( ( sqrt ` ( # ` I ) ) x. ( F D G ) ) ) )

  proof
    wph
    cF
    cX
    wcel
    #
    cG
    cX
    wcel
    #
    wa
    #
    wa
    #
    cF
    cG
    cD
    co
    #
    cF
    cG
    cI
    crrn
    cfv
    #
    co
    #
    cle
    wbr
    @6
    cI
    chash
    cfv
    #
    csqrt
    cfv
    #
    @4
    cmul
    co
    #
    cle
    wbr
    #
    @3
    @4
    vk
    cI
    vk
    cv
    #
    cF
    cfv
    #
    @11
    cG
    cfv
    #
    cabs
    cmin
    ccom
    #
    cr
    cr
    cxp
    #
    cres
    #
    co
    #
    cmpt
    #
    crn
    #
    cc0
    csn
    #
    cun
    #
    cxr
    clt
    csup
    #
    @6
    cle
    @3
    @4
    cF
    cG
    ccnfld
    csca
    cfv
    #
    cI
    ccnfld
    cr
    cress
    co
    #
    csn
    cxp
    #
    cprds
    co
    #
    cds
    cfv
    #
    co
    @22
    @3
    cD
    @27
    cF
    cG
    @3
    cD
    cY
    cds
    cfv
    @27
    rrnequiv.d
    @3
    cY
    @26
    cds
    @3
    @24
    cvv
    wcel
    #
    cI
    cfn
    wcel
    #
    cY
    @26
    wceq
    ccnfld
    cr
    cress
    ovex
    #
    wph
    @29
    @2
    rrnequiv.i
    adantr
    #
    @24
    @23
    cI
    cvv
    cfn
    cY
    rrnequiv.y
    cr
    cvv
    wcel
    #
    @23
    @24
    csca
    cfv
    wceq
    reex
    cr
    @23
    ccnfld
    @24
    cvv
    @24
    eqid
    #
    @23
    eqid
    resssca
    ax-mp
    pwsval
    sylancr
    #
    fveq2d
    syl5eq
    oveqd
    @3
    vk
    @26
    cbs
    cfv
    #
    @27
    @24
    @23
    @16
    cF
    cG
    cI
    cr
    cvv
    cfn
    cvv
    @26
    @25
    vk
    cI
    @24
    cmpt
    @23
    cprds
    vk
    cI
    @24
    fconstmpt
    oveq2i
    #
    @35
    eqid
    #
    @3
    ccnfld
    csca
    fvexd
    #
    @31
    @3
    @28
    vk
    cI
    @28
    @3
    @11
    cI
    wcel
    #
    wa
    #
    @30
    a1i
    ralrimiva
    #
    @3
    cF
    cX
    @35
    wph
    @0
    @1
    simprl
    #
    @3
    cX
    cr
    cI
    cmap
    co
    #
    @35
    rrnequiv.1
    @3
    @43
    cY
    cbs
    cfv
    #
    @35
    @3
    @28
    @29
    @43
    @44
    wceq
    @30
    @31
    cr
    @24
    cI
    cvv
    cfn
    cY
    rrnequiv.y
    cr
    cc
    wss
    cr
    @24
    cbs
    cfv
    wceq
    ax-resscn
    cr
    cc
    @24
    ccnfld
    @33
    cnfldbas
    ressbas2
    ax-mp
    #
    pwsbas
    sylancr
    @3
    cY
    @26
    cbs
    @34
    fveq2d
    eqtrd
    syl5eq
    #
    eleqtrd
    #
    @3
    cG
    cX
    @35
    wph
    @0
    @1
    simprr
    #
    @46
    eleqtrd
    #
    @45
    @14
    @24
    cds
    cfv
    #
    @15
    @32
    @14
    @50
    wceq
    reex
    cr
    @14
    ccnfld
    @24
    cvv
    @33
    cnfldds
    ressds
    ax-mp
    reseq1i
    @27
    eqid
    prdsdsval3
    eqtrd
    #
    @3
    @22
    @6
    cle
    wbr
    #
    vz
    cv
    #
    @6
    cle
    wbr
    #
    vz
    @21
    wral
    #
    @3
    @54
    vz
    @19
    wral
    #
    @54
    vz
    @20
    wral
    @55
    @3
    @17
    @6
    cle
    wbr
    #
    vk
    cI
    wral
    #
    @56
    @3
    @57
    vk
    cI
    wph
    @29
    @2
    @39
    @57
    rrnequiv.i
    @29
    @39
    @2
    @57
    @11
    cF
    cG
    cI
    @16
    cX
    rrnequiv.1
    @16
    eqid
    #
    rrndstprj1
    an32s
    sylanl1
    ralrimiva
    @17
    cvv
    wcel
    #
    vk
    cI
    wral
    @56
    @58
    wb
    @60
    vk
    cI
    @12
    @13
    @16
    ovex
    #
    rgenw
    @54
    @57
    vk
    vz
    cI
    @17
    @18
    cvv
    @18
    eqid
    #
    @53
    @17
    @6
    cle
    breq1
    ralrnmpt
    ax-mp
    sylibr
    @3
    @54
    vz
    @20
    @3
    @54
    @53
    @20
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @3
    @5
    cX
    cme
    cfv
    #
    wcel
    #
    @0
    @1
    @64
    @3
    @29
    @66
    @31
    cI
    cX
    rrnequiv.1
    rrnmet
    syl
    #
    @42
    @48
    cF
    cG
    @5
    cX
    metge0
    syl3anc
    @63
    @53
    cc0
    @6
    cle
    @53
    cc0
    elsni
    breq1d
    syl5ibrcom
    ralrimiv
    @54
    vz
    @19
    @20
    ralunb
    sylanbrc
    @3
    @21
    cxr
    wss
    #
    @6
    cxr
    wcel
    @52
    @55
    wb
    @3
    @19
    @20
    cxr
    @3
    @19
    cr
    cxr
    @3
    cI
    cr
    @18
    wf
    @19
    cr
    wss
    @3
    vk
    cI
    @17
    cr
    @18
    @40
    @12
    cr
    wcel
    #
    @13
    cr
    wcel
    #
    @17
    cr
    wcel
    #
    @3
    @69
    vk
    cI
    @3
    vk
    @35
    @24
    @23
    cF
    cI
    cr
    cvv
    cfn
    cvv
    @26
    @36
    @37
    @38
    @31
    @41
    @45
    @47
    prdsbascl
    r19.21bi
    @3
    @70
    vk
    cI
    @3
    vk
    @35
    @24
    @23
    cG
    cI
    cr
    cvv
    cfn
    cvv
    @26
    @36
    @37
    @38
    @31
    @41
    @45
    @49
    prdsbascl
    r19.21bi
    @16
    cr
    cme
    cfv
    wcel
    @69
    @70
    @71
    @16
    @59
    remet
    @12
    @13
    @16
    cr
    metcl
    mp3an1
    syl2anc
    #
    @62
    fmptd
    cI
    cr
    @18
    frn
    syl
    ressxr
    syl6ss
    @3
    cc0
    cxr
    cc0
    cxr
    wcel
    @3
    0xr
    a1i
    snssd
    unssd
    #
    @3
    cr
    cxr
    @6
    ressxr
    @3
    @66
    @0
    @1
    @6
    cr
    wcel
    #
    @67
    @42
    @48
    cF
    cG
    @5
    cX
    metcl
    syl3anc
    #
    sseldi
    vz
    @21
    @6
    supxrleub
    syl2anc
    mpbird
    eqbrtrd
    @3
    @10
    cI
    c0
    @3
    cI
    c0
    wceq
    #
    wa
    #
    @6
    cG
    cG
    @5
    co
    #
    @9
    cle
    @77
    cF
    cG
    cG
    @5
    @3
    @76
    cF
    cG
    wceq
    #
    @76
    @79
    @3
    @12
    @13
    wceq
    #
    vk
    cI
    wral
    #
    @80
    vk
    cI
    rzal
    @3
    cF
    cI
    wfn
    #
    cG
    cI
    wfn
    #
    @79
    @81
    wb
    @3
    cF
    @43
    wcel
    cI
    cr
    cF
    wf
    @82
    @3
    cF
    cX
    @43
    @42
    rrnequiv.1
    syl6eleq
    cF
    cr
    cI
    elmapi
    cI
    cr
    cF
    ffn
    3syl
    @3
    cG
    @43
    wcel
    cI
    cr
    cG
    wf
    @83
    @3
    cG
    cX
    @43
    @48
    rrnequiv.1
    syl6eleq
    cG
    cr
    cI
    elmapi
    cI
    cr
    cG
    ffn
    3syl
    vk
    cI
    cF
    cG
    eqfnfv
    syl2anc
    syl5ibr
    imp
    oveq1d
    @3
    @78
    @9
    cle
    wbr
    @76
    @3
    @78
    cc0
    @9
    cle
    @3
    @66
    @1
    @78
    cc0
    wceq
    @67
    @48
    cG
    @5
    cX
    met0
    syl2anc
    @3
    @8
    @4
    @3
    @7
    @3
    @7
    @3
    @29
    @7
    cn0
    wcel
    @31
    cI
    hashcl
    syl
    #
    nn0red
    #
    @3
    @7
    @84
    nn0ge0d
    #
    resqrtcld
    #
    @3
    cD
    @65
    wcel
    #
    @0
    @1
    @4
    cr
    wcel
    #
    @3
    @29
    @88
    @31
    cD
    cI
    cX
    cY
    rrnequiv.y
    rrnequiv.d
    rrnequiv.1
    repwsmet
    syl
    #
    @42
    @48
    cF
    cG
    cD
    cX
    metcl
    syl3anc
    #
    @3
    @7
    @85
    @86
    sqrtge0d
    @3
    @88
    @0
    @1
    cc0
    @4
    cle
    wbr
    #
    @90
    @42
    @48
    cF
    cG
    cD
    cX
    metge0
    syl3anc
    #
    mulge0d
    eqbrtrd
    adantr
    eqbrtrd
    @3
    cI
    c0
    wne
    #
    wa
    #
    @10
    @6
    @9
    vr
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vr
    crp
    wral
    #
    @95
    @98
    vr
    crp
    @3
    @94
    @96
    crp
    wcel
    #
    @98
    @3
    @94
    @100
    wa
    #
    wa
    #
    @6
    @97
    @3
    @74
    @101
    @75
    adantr
    @102
    @9
    @96
    @3
    @9
    cr
    wcel
    #
    @101
    @3
    @8
    @4
    @87
    @91
    remulcld
    #
    adantr
    @100
    @96
    cr
    wcel
    @3
    @94
    @96
    rpre
    ad2antll
    #
    readdcld
    @102
    @6
    @4
    @96
    @8
    cdiv
    co
    #
    caddc
    co
    #
    @8
    cmul
    co
    #
    @97
    clt
    @102
    cI
    cfn
    c0
    csn
    cdif
    wcel
    #
    @0
    @1
    @107
    crp
    wcel
    @17
    @107
    clt
    wbr
    #
    vk
    cI
    wral
    @6
    @108
    clt
    wbr
    @102
    @29
    @94
    @109
    @3
    @29
    @101
    @31
    adantr
    #
    @3
    @94
    @100
    simprl
    #
    cI
    cfn
    c0
    eldifsn
    sylanbrc
    @3
    @0
    @101
    @42
    adantr
    @3
    @1
    @101
    @48
    adantr
    @102
    @107
    @102
    @4
    @106
    @3
    @89
    @101
    @91
    adantr
    #
    @102
    @106
    @102
    @96
    @8
    @3
    @94
    @100
    simprr
    @102
    @7
    @102
    @7
    @102
    @7
    cn
    wcel
    #
    @94
    @112
    @102
    @29
    @114
    @94
    wb
    @111
    cI
    hashnncl
    syl
    mpbird
    nnrpd
    rpsqrtcld
    #
    rpdivcld
    #
    rpred
    #
    readdcld
    #
    @102
    cc0
    @4
    @107
    @102
    0red
    @113
    @118
    @3
    @92
    @101
    @93
    adantr
    @102
    @4
    @106
    @113
    @116
    ltaddrpd
    #
    lelttrd
    elrpd
    @102
    @110
    vk
    cI
    @102
    @39
    wa
    #
    @17
    @4
    @107
    @3
    @39
    @71
    @101
    @72
    adantlr
    @102
    @89
    @39
    @113
    adantr
    @102
    @107
    cr
    wcel
    @39
    @118
    adantr
    @120
    @17
    @22
    @4
    cle
    @120
    @68
    @17
    @21
    wcel
    @17
    @22
    cle
    wbr
    @3
    @68
    @101
    @39
    @73
    ad2antrr
    @120
    @19
    @21
    @17
    @19
    @20
    ssun1
    @120
    @39
    @60
    @17
    @19
    wcel
    @102
    @39
    simpr
    @61
    vk
    cI
    @17
    @18
    cvv
    @62
    elrnmpt1
    sylancl
    sseldi
    @21
    @17
    supxrub
    syl2anc
    @3
    @4
    @22
    wceq
    @101
    @39
    @51
    ad2antrr
    breqtrrd
    @102
    @4
    @107
    clt
    wbr
    @39
    @119
    adantr
    lelttrd
    ralrimiva
    @107
    vk
    cF
    cG
    cI
    @16
    cX
    rrnequiv.1
    @59
    rrndstprj2
    syl32anc
    @102
    @108
    @4
    @8
    cmul
    co
    #
    @106
    @8
    cmul
    co
    #
    caddc
    co
    @97
    @102
    @4
    @106
    @8
    @102
    @4
    @113
    recnd
    #
    @102
    @106
    @117
    recnd
    @102
    @8
    @3
    @8
    cr
    wcel
    @101
    @87
    adantr
    recnd
    #
    adddird
    @102
    @121
    @9
    @122
    @96
    caddc
    @102
    @4
    @8
    @123
    @124
    mulcomd
    @102
    @96
    @8
    @102
    @96
    @105
    recnd
    @124
    @102
    @8
    @115
    rpne0d
    divcan1d
    oveq12d
    eqtrd
    breqtrd
    ltled
    anassrs
    ralrimiva
    @3
    @10
    @99
    wb
    #
    @94
    @3
    @74
    @103
    @125
    @75
    @104
    vr
    @6
    @9
    alrple
    syl2anc
    adantr
    mpbird
    pm2.61dane
    jca
end
