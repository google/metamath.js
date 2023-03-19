include "cun.mm"
include "wss.mm"
include "wcel.mm"
include "wo.mm"
include "wn.mm"
include "cv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "cmnf.mm"
include "cioo.mm"
include "cin.mm"
include "crp.mm"
include "wrex.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cicc.mm"
include "csup.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "inss2.mm"
include "sseldi.mm"
include "wceq.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "sstrd.mm"
include "syl5ss.mm"
include "inss1.mm"
include "cxr.mm"
include "sseldd.mm"
include "rexrd.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "elind.mm"
include "ne0i.mm"
include "syl.mm"
include "sseli.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "simp3.mm"
include "syl6bi.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprcl.mm"
include "syl5eqel.mm"
include "rphalfcl.mm"
include "ltaddrp.mm"
include "syl2an.mm"
include "adantr.mm"
include "rpred.mm"
include "readdcl.mm"
include "ltnled.mm"
include "mpbid.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "ltled.mm"
include "letrd.mm"
include "eliooord.mm"
include "simprd.mm"
include "mpbir3and.mm"
include "mtand.mm"
include "eqid.mm"
include "remetdval.mm"
include "recnd.mm"
include "adantl.mm"
include "pncan2d.mm"
include "fveq2d.mm"
include "rpre.mm"
include "rpge0.mm"
include "absidd.mm"
include "3eqtrd.mm"
include "rphalflt.mm"
include "eqbrtrd.mm"
include "cxmt.mm"
include "rexmet.mm"
include "a1i.mm"
include "rpxr.mm"
include "elbl3.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "ssel.mm"
include "syl5com.mm"
include "mtod.mm"
include "nrexdv.mm"
include "mnflt.mm"
include "suprleub.mm"
include "syl5eqbr.mm"
include "leloed.mm"
include "ord.mm"
include "cdif.mm"
include "elndif.mm"
include "elin.mm"
include "sseld.mm"
include "syl5bir.mm"
include "mpan2d.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "con4d.mm"
include "imp.mm"
include "mnfxr.mm"
include "elioo2.mm"
include "sylancr.mm"
include "ex.mm"
include "ancld.mm"
include "crn.mm"
include "ctg.mm"
include "wi.mm"
include "ctop.mm"
include "retop.mm"
include "iooretop.mm"
include "inopn.mm"
include "mp3an13.mm"
include "cmopn.mm"
include "tgioo.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "3syl.mm"
include "ltsubrp.mm"
include "sylan.mm"
include "resubcl.mm"
include "bl2ioo.mm"
include "sselda.mm"
include "ad3antrrr.mm"
include "simprl.mm"
include "simplr.mm"
include "adantrr.mm"
include "simprr.mm"
include "simpllr.mm"
include "readdcld.mm"
include "ltaddrpd.mm"
include "lelttrd.mm"
include "rexr.mm"
include "expr.mm"
include "lenltd.mm"
include "ralrimiva.mm"
include "sylbid.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "elun.mm"
include "sylnibr.mm"

theorem reconnlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cV: class V
  let vw: setvar w
  let vz: setvar z
  let vr: setvar r
  assume reconnlem2.1: |- ( ph -> A C_ RR )
  assume reconnlem2.2: |- ( ph -> U e. ( topGen ` ran (,) ) )
  assume reconnlem2.3: |- ( ph -> V e. ( topGen ` ran (,) ) )
  assume reconnlem2.4: |- ( ph -> A. x e. A A. y e. A ( x [,] y ) C_ A )
  assume reconnlem2.5: |- ( ph -> B e. ( U i^i A ) )
  assume reconnlem2.6: |- ( ph -> C e. ( V i^i A ) )
  assume reconnlem2.7: |- ( ph -> ( U i^i V ) C_ ( RR \ A ) )
  assume reconnlem2.8: |- ( ph -> B <_ C )
  assume reconnlem2.9: |- S = sup ( ( U i^i ( B [,] C ) ) , RR , < )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint C r
  disjoint C w
  disjoint C z
  disjoint ph r
  disjoint ph w
  disjoint U r
  disjoint U w
  disjoint U z
  disjoint S r
  disjoint S w
  disjoint V r
  disjoint V w
  assert |- ( ph -> -. A C_ ( U u. V ) )

  proof
    wph
    cA
    cU
    cV
    cun
    #
    wss
    #
    cS
    @0
    wcel
    #
    wph
    cS
    cU
    wcel
    #
    cS
    cV
    wcel
    #
    wo
    #
    @2
    wph
    @3
    wn
    #
    @4
    wn
    @5
    wn
    wph
    @3
    cS
    vr
    cv
    #
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    cbl
    cfv
    co
    #
    cU
    cmnf
    cC
    cioo
    co
    #
    cin
    #
    wss
    #
    vr
    crp
    wrex
    #
    wph
    @12
    vr
    crp
    wph
    @7
    crp
    wcel
    #
    wa
    #
    @12
    cS
    @7
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @11
    wcel
    #
    @15
    @18
    @17
    cS
    cle
    wbr
    #
    @15
    cS
    @17
    clt
    wbr
    #
    @19
    wn
    wph
    cS
    cr
    wcel
    #
    @16
    crp
    wcel
    #
    @20
    @14
    wph
    cS
    cU
    cB
    cC
    cicc
    co
    #
    cin
    #
    cr
    clt
    csup
    #
    cr
    reconnlem2.9
    wph
    @24
    cr
    wss
    #
    @24
    c0
    wne
    #
    vw
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    vw
    @24
    wral
    #
    vz
    cr
    wrex
    #
    @25
    cr
    wcel
    wph
    @24
    @23
    cr
    cU
    @23
    inss2
    #
    wph
    @23
    cA
    cr
    wph
    cB
    cA
    wcel
    cC
    cA
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cicc
    co
    #
    cA
    wss
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @23
    cA
    wss
    #
    wph
    cU
    cA
    cin
    #
    cA
    cB
    cU
    cA
    inss2
    reconnlem2.5
    sseldi
    #
    wph
    cV
    cA
    cin
    #
    cA
    cC
    cV
    cA
    inss2
    reconnlem2.6
    sseldi
    #
    reconnlem2.4
    @38
    @39
    cB
    @36
    cicc
    co
    #
    cA
    wss
    vx
    vy
    cB
    cC
    cA
    cA
    @35
    cB
    wceq
    @37
    @44
    cA
    @35
    cB
    @36
    cicc
    oveq1
    sseq1d
    @36
    cC
    wceq
    @44
    @23
    cA
    @36
    cC
    cB
    cicc
    oveq2
    sseq1d
    rspc2va
    syl21anc
    #
    reconnlem2.1
    sstrd
    syl5ss
    #
    wph
    cB
    @24
    wcel
    #
    @27
    wph
    cU
    @23
    cB
    wph
    @40
    cU
    cB
    cU
    cA
    inss1
    reconnlem2.5
    sseldi
    wph
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    #
    cB
    cC
    cle
    wbr
    cB
    @23
    wcel
    wph
    cB
    wph
    cA
    cr
    cB
    reconnlem2.1
    @41
    sseldd
    #
    rexrd
    wph
    cC
    wph
    cA
    cr
    cC
    reconnlem2.1
    @43
    sseldd
    #
    rexrd
    #
    reconnlem2.8
    cB
    cC
    lbicc2
    syl3anc
    elind
    #
    @24
    cB
    ne0i
    syl
    #
    wph
    cC
    cr
    wcel
    #
    @28
    cC
    cle
    wbr
    #
    vw
    @24
    wral
    #
    @32
    @50
    wph
    @55
    vw
    @24
    @28
    @24
    wcel
    #
    @28
    @23
    wcel
    #
    wph
    @55
    @24
    @23
    @28
    @33
    sseli
    wph
    @58
    @28
    cr
    wcel
    #
    cB
    @28
    cle
    wbr
    #
    @55
    w3a
    #
    @55
    wph
    cB
    cr
    wcel
    #
    @54
    @58
    @61
    wb
    @49
    @50
    cB
    cC
    @28
    elicc2
    syl2anc
    @59
    @60
    @55
    simp3
    syl6bi
    syl5
    ralrimiv
    #
    @31
    @56
    vz
    cC
    cr
    @29
    cC
    wceq
    @30
    @55
    vw
    @24
    @29
    cC
    @28
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    vz
    vw
    @24
    suprcl
    syl3anc
    syl5eqel
    #
    @7
    rphalfcl
    #
    cS
    @16
    ltaddrp
    syl2an
    #
    @15
    cS
    @17
    wph
    @21
    @14
    @65
    adantr
    #
    wph
    @21
    @16
    cr
    wcel
    #
    @17
    cr
    wcel
    #
    @14
    @65
    @14
    @16
    @66
    rpred
    #
    cS
    @16
    readdcl
    syl2an
    #
    ltnled
    mpbid
    @15
    @18
    wa
    #
    @17
    @25
    cS
    cle
    @73
    @26
    @27
    @32
    @17
    @24
    wcel
    @17
    @25
    cle
    wbr
    wph
    @26
    @14
    @18
    @46
    ad2antrr
    wph
    @27
    @14
    @18
    @53
    ad2antrr
    wph
    @32
    @14
    @18
    @64
    ad2antrr
    @73
    cU
    @23
    @17
    @73
    @11
    cU
    @17
    cU
    @10
    inss1
    @15
    @18
    simpr
    #
    sseldi
    @73
    @17
    @23
    wcel
    #
    @70
    cB
    @17
    cle
    wbr
    #
    @17
    cC
    cle
    wbr
    #
    @15
    @70
    @18
    @72
    adantr
    #
    @73
    cB
    cS
    @17
    wph
    @62
    @14
    @18
    @49
    ad2antrr
    #
    wph
    @21
    @14
    @18
    @65
    ad2antrr
    #
    @78
    wph
    cB
    cS
    cle
    wbr
    #
    @14
    @18
    wph
    cB
    @25
    cS
    cle
    wph
    @26
    @27
    @32
    @47
    cB
    @25
    cle
    wbr
    @46
    @53
    @64
    @52
    vz
    vw
    @24
    cB
    suprub
    syl31anc
    reconnlem2.9
    syl6breqr
    #
    ad2antrr
    @73
    cS
    @17
    @80
    @78
    @15
    @20
    @18
    @67
    adantr
    ltled
    letrd
    @73
    @17
    cC
    @78
    wph
    @54
    @14
    @18
    @50
    ad2antrr
    #
    @73
    @17
    @10
    wcel
    #
    @17
    cC
    clt
    wbr
    #
    @73
    @11
    @10
    @17
    cU
    @10
    inss2
    @74
    sseldi
    @84
    cmnf
    @17
    clt
    wbr
    @85
    @17
    cmnf
    cC
    eliooord
    simprd
    syl
    ltled
    @73
    @62
    @54
    @75
    @70
    @76
    @77
    w3a
    wb
    @79
    @83
    cB
    cC
    @17
    elicc2
    syl2anc
    mpbir3and
    elind
    vz
    vw
    @24
    @17
    suprub
    syl31anc
    reconnlem2.9
    syl6breqr
    mtand
    @15
    @17
    @9
    wcel
    #
    @12
    @18
    @15
    @86
    @17
    cS
    @8
    co
    #
    @7
    clt
    wbr
    #
    @15
    @87
    @16
    @7
    clt
    @15
    @87
    @17
    cS
    cmin
    co
    #
    cabs
    cfv
    #
    @16
    cabs
    cfv
    #
    @16
    @15
    @70
    @21
    @87
    @90
    wceq
    @72
    @68
    @17
    cS
    @8
    @8
    eqid
    #
    remetdval
    syl2anc
    @15
    @89
    @16
    cabs
    @15
    cS
    @16
    @15
    cS
    @68
    recnd
    @15
    @16
    @14
    @69
    wph
    @71
    adantl
    recnd
    pncan2d
    fveq2d
    @15
    @22
    @91
    @16
    wceq
    @14
    @22
    wph
    @66
    adantl
    @22
    @16
    @16
    rpre
    @16
    rpge0
    absidd
    syl
    3eqtrd
    @14
    @16
    @7
    clt
    wbr
    wph
    @7
    rphalflt
    adantl
    eqbrtrd
    @15
    @8
    cr
    cxmt
    cfv
    wcel
    #
    @7
    cxr
    wcel
    #
    @21
    @70
    @86
    @88
    wb
    @93
    @15
    @8
    @92
    rexmet
    #
    a1i
    @14
    @94
    wph
    @7
    rpxr
    adantl
    @68
    @72
    @17
    @8
    cS
    @7
    cr
    elbl3
    syl22anc
    mpbird
    @9
    @11
    @17
    ssel
    syl5com
    mtod
    nrexdv
    wph
    @3
    @3
    cS
    @10
    wcel
    #
    wa
    #
    @13
    wph
    @3
    @96
    wph
    @3
    @96
    wph
    @3
    wa
    #
    @96
    @21
    cmnf
    cS
    clt
    wbr
    #
    cS
    cC
    clt
    wbr
    #
    wph
    @21
    @3
    @65
    adantr
    #
    @98
    @21
    @99
    @101
    cS
    mnflt
    syl
    wph
    @3
    @100
    wph
    @100
    @3
    wph
    @100
    wn
    cS
    cC
    wceq
    #
    @6
    wph
    @100
    @102
    wph
    cS
    cC
    cle
    wbr
    #
    @100
    @102
    wo
    wph
    cS
    @25
    cC
    cle
    reconnlem2.9
    wph
    @25
    cC
    cle
    wbr
    #
    @56
    @63
    wph
    @26
    @27
    @32
    @54
    @104
    @56
    wb
    @46
    @53
    @64
    @50
    vz
    vw
    vw
    @24
    cC
    suprleub
    syl31anc
    mpbird
    syl5eqbr
    #
    wph
    cS
    cC
    @65
    @50
    leloed
    mpbid
    ord
    wph
    @6
    @102
    cC
    cU
    wcel
    #
    wn
    wph
    @106
    cC
    cr
    cA
    cdif
    #
    wcel
    #
    wph
    @34
    @108
    wn
    @43
    cC
    cA
    cr
    elndif
    syl
    wph
    @106
    cC
    cV
    wcel
    #
    @108
    wph
    @42
    cV
    cC
    cV
    cA
    inss1
    reconnlem2.6
    sseldi
    @106
    @109
    wa
    cC
    cU
    cV
    cin
    #
    wcel
    wph
    @108
    cC
    cU
    cV
    elin
    wph
    @110
    @107
    cC
    reconnlem2.7
    sseld
    syl5bir
    mpan2d
    mtod
    @102
    @3
    @106
    cS
    cC
    cU
    eleq1
    notbid
    syl5ibrcom
    syld
    con4d
    imp
    wph
    @96
    @21
    @99
    @100
    w3a
    wb
    #
    @3
    wph
    cmnf
    cxr
    wcel
    @48
    @111
    mnfxr
    @51
    cmnf
    cC
    cS
    elioo2
    sylancr
    adantr
    mpbir3and
    ex
    ancld
    @97
    cS
    @11
    wcel
    #
    wph
    @13
    cS
    cU
    @10
    elin
    wph
    cU
    cioo
    crn
    ctg
    cfv
    #
    wcel
    #
    @11
    @113
    wcel
    #
    @112
    @13
    wi
    reconnlem2.2
    @113
    ctop
    wcel
    @114
    @10
    @113
    wcel
    @115
    retop
    cmnf
    cC
    iooretop
    cU
    @10
    @113
    inopn
    mp3an13
    @115
    @112
    @13
    @93
    @115
    @112
    @13
    @95
    vr
    @11
    @8
    cS
    @113
    cr
    @8
    @8
    cmopn
    cfv
    #
    @92
    @116
    eqid
    tgioo
    #
    mopni2
    mp3an1
    ex
    3syl
    syl5bir
    syld
    mtod
    wph
    @4
    @9
    cV
    wss
    #
    vr
    crp
    wrex
    #
    wph
    @118
    vr
    crp
    @15
    @118
    cS
    cS
    @7
    cmin
    co
    #
    cle
    wbr
    #
    @15
    @120
    cS
    clt
    wbr
    #
    @121
    wn
    wph
    @21
    @14
    @122
    @65
    cS
    @7
    ltsubrp
    sylan
    @15
    @120
    cS
    wph
    @21
    @7
    cr
    wcel
    #
    @120
    cr
    wcel
    #
    @14
    @65
    @7
    rpre
    #
    cS
    @7
    resubcl
    syl2an
    #
    @68
    ltnled
    mpbid
    @15
    @118
    @120
    cS
    @7
    caddc
    co
    #
    cioo
    co
    #
    cV
    wss
    #
    @121
    @15
    @9
    @128
    cV
    wph
    @21
    @123
    @9
    @128
    wceq
    @14
    @65
    @125
    cS
    @7
    @8
    @92
    bl2ioo
    syl2an
    sseq1d
    @15
    @129
    @121
    @15
    @129
    wa
    #
    cS
    @25
    @120
    cle
    reconnlem2.9
    @130
    @25
    @120
    cle
    wbr
    #
    @28
    @120
    cle
    wbr
    #
    vw
    @24
    wral
    #
    @130
    @132
    vw
    @24
    @130
    @57
    wa
    #
    @132
    @120
    @28
    clt
    wbr
    #
    wn
    @134
    @135
    @28
    @107
    wcel
    #
    @134
    @28
    cA
    wcel
    @136
    wn
    @130
    @24
    cA
    @28
    @130
    @24
    @23
    cA
    @33
    wph
    @39
    @14
    @129
    @45
    ad2antrr
    syl5ss
    sselda
    @28
    cA
    cr
    elndif
    syl
    @130
    @57
    @135
    @136
    @130
    @57
    @135
    wa
    #
    wa
    #
    @110
    @107
    @28
    wph
    @110
    @107
    wss
    @14
    @129
    @137
    reconnlem2.7
    ad3antrrr
    @138
    cU
    cV
    @28
    @138
    @24
    cU
    @28
    cU
    @23
    inss1
    @130
    @57
    @135
    simprl
    #
    sseldi
    @138
    @128
    cV
    @28
    @15
    @129
    @137
    simplr
    @138
    @28
    @128
    wcel
    #
    @59
    @135
    @28
    @127
    clt
    wbr
    #
    @130
    @57
    @59
    @135
    @134
    @24
    cr
    @28
    wph
    @26
    @14
    @129
    @57
    @46
    ad3antrrr
    #
    @130
    @57
    simpr
    sseldd
    #
    adantrr
    #
    @130
    @57
    @135
    simprr
    @138
    @28
    cS
    @127
    @144
    @15
    @21
    @129
    @137
    @68
    ad2antrr
    #
    @138
    cS
    @7
    @145
    @138
    @7
    wph
    @14
    @129
    @137
    simpllr
    #
    rpred
    readdcld
    #
    @138
    @28
    @25
    cS
    cle
    @138
    @26
    @27
    @32
    @57
    @28
    @25
    cle
    wbr
    @130
    @57
    @26
    @135
    @142
    adantrr
    wph
    @27
    @14
    @129
    @137
    @53
    ad3antrrr
    wph
    @32
    @14
    @129
    @137
    @64
    ad3antrrr
    @139
    vz
    vw
    @24
    @28
    suprub
    syl31anc
    reconnlem2.9
    syl6breqr
    @138
    cS
    @7
    @145
    @146
    ltaddrpd
    lelttrd
    @138
    @124
    @127
    cr
    wcel
    #
    @140
    @59
    @135
    @141
    w3a
    wb
    #
    @15
    @124
    @129
    @137
    @126
    ad2antrr
    @147
    @124
    @120
    cxr
    wcel
    @127
    cxr
    wcel
    @149
    @148
    @120
    rexr
    @127
    rexr
    @120
    @127
    @28
    elioo2
    syl2an
    syl2anc
    mpbir3and
    sseldd
    elind
    sseldd
    expr
    mtod
    @134
    @28
    @120
    @143
    @15
    @124
    @129
    @57
    @126
    ad2antrr
    lenltd
    mpbird
    ralrimiva
    @130
    @26
    @27
    @32
    @124
    @131
    @133
    wb
    wph
    @26
    @14
    @129
    @46
    ad2antrr
    wph
    @27
    @14
    @129
    @53
    ad2antrr
    wph
    @32
    @14
    @129
    @64
    ad2antrr
    @15
    @124
    @129
    @126
    adantr
    vz
    vw
    vw
    @24
    @120
    suprleub
    syl31anc
    mpbird
    syl5eqbr
    ex
    sylbid
    mtod
    nrexdv
    wph
    cV
    @113
    wcel
    #
    @4
    @119
    wi
    reconnlem2.3
    @150
    @4
    @119
    @93
    @150
    @4
    @119
    @95
    vr
    cV
    @8
    cS
    @113
    cr
    @117
    mopni2
    mp3an1
    ex
    syl
    mtod
    @3
    @4
    ioran
    sylanbrc
    cS
    cU
    cV
    elun
    sylnibr
    wph
    cS
    cA
    wcel
    @1
    @2
    wph
    @23
    cA
    cS
    @45
    wph
    cS
    @23
    wcel
    #
    @21
    @81
    @103
    @65
    @82
    @105
    wph
    @62
    @54
    @151
    @21
    @81
    @103
    w3a
    wb
    @49
    @50
    cB
    cC
    cS
    elicc2
    syl2anc
    mpbir3and
    sseldd
    cA
    @0
    cS
    ssel
    syl5com
    mtod
end
