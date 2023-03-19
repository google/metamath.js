include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cioo.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "ssrab2.mm"
include "cz.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cfz.mm"
include "fzossfz.mm"
include "fzssz.mm"
include "sstri.mm"
include "a1i.mm"
include "cuz.mm"
include "0z.mm"
include "0le0.mm"
include "eluz2.mm"
include "mpbir3an.mm"
include "nnzd.mm"
include "nngt0d.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "cicc.mm"
include "cpr.mm"
include "crn.mm"
include "cin.mm"
include "cun.mm"
include "wa.mm"
include "cxr.mm"
include "rexrd.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "ubicc2.mm"
include "jca.mm"
include "wb.mm"
include "prssg.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "inss2.mm"
include "ioossicc.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "iccssred.mm"
include "sstrd.mm"
include "wiso.mm"
include "wf1o.mm"
include "wf.mm"
include "isof1o.mm"
include "f1of.mm"
include "3syl.mm"
include "elfzofz.mm"
include "syl.mm"
include "sseldd.mm"
include "iccgelb.mm"
include "letrd.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "nnred.mm"
include "sseli.mm"
include "elfzo0le.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprzcl.mm"
include "syl5eqel.mm"
include "fzofzp1.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "nfsup.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfbr.mm"
include "elrabf.mm"
include "sylib.mm"
include "simprd.mm"
include "wn.mm"
include "simpr.mm"
include "adantr.mm"
include "iccssxr.mm"
include "syl6ss.mm"
include "xrltnle.mm"
include "mpbird.mm"
include "wfo.mm"
include "f1ofo.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "fdm.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "fvelrn.mm"
include "zre.mm"
include "ltp1d.mm"
include "adantlr.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "nltled.mm"
include "1red.mm"
include "readdcld.mm"
include "elfzoelz.mm"
include "zred.mm"
include "ssriv.mm"
include "isorel.mm"
include "syl12anc.mm"
include "iccleub.mm"
include "ltletrd.mm"
include "lelttrd.mm"
include "fzval3.mm"
include "elfzonelfzo.mm"
include "sylc.mm"
include "elfz1eq.mm"
include "fveq2d.mm"
include "breqtrd.mm"
include "lensymd.mm"
include "condan.mm"
include "nfov.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "syldan.mm"
include "mpdan.mm"
include "eliood.mm"
include "elind.mm"
include "elun2.mm"
include "syl6eleqr.mm"
include "foelrn.mm"
include "anim1i.mm"
include "adantllr.mm"
include "eqcom.mm"
include "biimpi.mm"
include "simpl.mm"
include "eqbrtrd.mm"
include "adantll.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "simprl.mm"
include "simprr.mm"
include "btwnnz.mm"
include "pm2.65da.mm"
include "nrexdv.mm"
include "ioossioo.mm"
include "syl22anc.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "sseq2d.mm"

theorem fourierdlem20
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vk: setvar k
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vx: setvar x
  assume fourierdlem20.m: |- ( ph -> M e. NN )
  assume fourierdlem20.a: |- ( ph -> A e. RR )
  assume fourierdlem20.b: |- ( ph -> B e. RR )
  assume fourierdlem20.aleb: |- ( ph -> A <_ B )
  assume fourierdlem20.q: |- ( ph -> Q : ( 0 ... M ) --> RR )
  assume fourierdlem20.q0: |- ( ph -> ( Q ` 0 ) <_ A )
  assume fourierdlem20.qm: |- ( ph -> B <_ ( Q ` M ) )
  assume fourierdlem20.j: |- ( ph -> J e. ( 0 ..^ N ) )
  assume fourierdlem20.t: |- T = ( { A , B } u. ( ran Q i^i ( A (,) B ) ) )
  assume fourierdlem20.s: |- ( ph -> S Isom < , < ( ( 0 ... N ) , T ) )
  assume fourierdlem20.i: |- I = sup ( { k e. ( 0 ..^ M ) | ( Q ` k ) <_ ( S ` J ) } , RR , < )

  disjoint I i
  disjoint J i
  disjoint J k
  disjoint M i
  disjoint M k
  disjoint Q i
  disjoint Q k
  disjoint S i
  disjoint S k
  disjoint I j
  disjoint J j
  disjoint J x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint M j
  disjoint M x
  disjoint N j
  disjoint Q j
  disjoint Q x
  disjoint S j
  disjoint S x
  disjoint T j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> E. i e. ( 0 ..^ M ) ( ( S ` J ) (,) ( S ` ( J + 1 ) ) ) C_ ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) )

  proof
    wph
    cI
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    cJ
    cS
    cfv
    #
    cJ
    c1
    caddc
    co
    #
    cS
    cfv
    #
    cioo
    co
    #
    cI
    cQ
    cfv
    #
    cI
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    wss
    #
    @5
    vi
    cv
    #
    cQ
    cfv
    #
    @11
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    wss
    #
    vi
    @0
    wrex
    wph
    cI
    vk
    cv
    #
    cQ
    cfv
    #
    @2
    cle
    wbr
    #
    vk
    @0
    crab
    #
    cr
    clt
    csup
    #
    @0
    fourierdlem20.i
    wph
    @20
    @0
    @21
    @19
    vk
    @0
    ssrab2
    #
    wph
    @20
    cz
    wss
    #
    @20
    c0
    wne
    #
    vj
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vj
    @20
    wral
    #
    vx
    cr
    wrex
    #
    @21
    @20
    wcel
    @23
    wph
    @20
    @0
    cz
    @22
    @0
    cc0
    cM
    cfz
    co
    #
    cz
    cc0
    cM
    fzossfz
    #
    cc0
    cM
    fzssz
    #
    sstri
    sstri
    a1i
    wph
    cc0
    @20
    wcel
    #
    @24
    wph
    cc0
    @0
    wcel
    #
    cc0
    cQ
    cfv
    #
    @2
    cle
    wbr
    #
    @33
    wph
    cc0
    cc0
    cuz
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    cc0
    cM
    clt
    wbr
    @34
    @37
    wph
    @37
    cc0
    cz
    wcel
    #
    @39
    cc0
    cc0
    cle
    wbr
    0z
    0z
    0le0
    cc0
    cc0
    eluz2
    mpbir3an
    a1i
    wph
    cM
    fourierdlem20.m
    nnzd
    #
    wph
    cM
    fourierdlem20.m
    nngt0d
    cc0
    cc0
    cM
    elfzo2
    syl3anbrc
    #
    wph
    @35
    cA
    @2
    wph
    @30
    cr
    cc0
    cQ
    fourierdlem20.q
    wph
    @0
    @30
    cc0
    @31
    @41
    sseldi
    ffvelrnd
    fourierdlem20.a
    wph
    cT
    cr
    @2
    wph
    cT
    cA
    cB
    cicc
    co
    #
    cr
    wph
    cT
    cA
    cB
    cpr
    #
    cQ
    crn
    #
    cA
    cB
    cioo
    co
    #
    cin
    #
    cun
    #
    @42
    fourierdlem20.t
    wph
    @43
    @46
    @42
    wph
    cA
    @42
    wcel
    #
    cB
    @42
    wcel
    #
    wa
    #
    @43
    @42
    wss
    #
    wph
    @48
    @49
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    @48
    wph
    cA
    fourierdlem20.a
    rexrd
    #
    wph
    cB
    fourierdlem20.b
    rexrd
    #
    fourierdlem20.aleb
    cA
    cB
    lbicc2
    syl3anc
    wph
    @52
    @53
    @54
    @49
    @55
    @56
    fourierdlem20.aleb
    cA
    cB
    ubicc2
    syl3anc
    jca
    wph
    @52
    @53
    @50
    @51
    wb
    @55
    @56
    cA
    cB
    @42
    cxr
    cxr
    prssg
    syl2anc
    mpbid
    @46
    @42
    wss
    wph
    @46
    @45
    @42
    @44
    @45
    inss2
    cA
    cB
    ioossicc
    sstri
    a1i
    unssd
    syl5eqss
    #
    wph
    cA
    cB
    fourierdlem20.a
    fourierdlem20.b
    iccssred
    #
    sstrd
    #
    wph
    cc0
    cN
    cfz
    co
    #
    cT
    cJ
    cS
    wph
    @60
    cT
    clt
    clt
    cS
    wiso
    #
    @60
    cT
    cS
    wf1o
    #
    @60
    cT
    cS
    wf
    fourierdlem20.s
    @60
    cT
    clt
    clt
    cS
    isof1o
    #
    @60
    cT
    cS
    f1of
    3syl
    #
    wph
    cJ
    cc0
    cN
    cfzo
    co
    wcel
    #
    cJ
    @60
    wcel
    #
    fourierdlem20.j
    cJ
    cc0
    cN
    elfzofz
    syl
    #
    ffvelrnd
    #
    sseldd
    fourierdlem20.q0
    wph
    @52
    @53
    @2
    @42
    wcel
    cA
    @2
    cle
    wbr
    @55
    @56
    wph
    cT
    @42
    @2
    @57
    @68
    sseldd
    #
    cA
    cB
    @2
    iccgelb
    syl3anc
    #
    letrd
    @19
    @36
    vk
    cc0
    @0
    @17
    cc0
    wceq
    @18
    @35
    @2
    cle
    @17
    cc0
    cQ
    fveq2
    breq1d
    elrab
    sylanbrc
    @20
    cc0
    ne0i
    syl
    #
    wph
    cM
    cr
    wcel
    @25
    cM
    cle
    wbr
    #
    vj
    @20
    wral
    #
    @29
    wph
    cM
    fourierdlem20.m
    nnred
    wph
    @72
    vj
    @20
    @25
    @20
    wcel
    #
    @72
    wph
    @74
    @25
    @0
    wcel
    #
    @72
    @20
    @0
    @25
    @22
    sseli
    @25
    cM
    elfzo0le
    syl
    adantl
    ralrimiva
    @28
    @73
    vx
    cM
    cr
    @26
    cM
    wceq
    @27
    @72
    vj
    @20
    @26
    cM
    @25
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    vx
    vj
    @20
    suprzcl
    syl3anc
    #
    sseldi
    syl5eqel
    #
    wph
    @6
    cxr
    wcel
    @8
    cxr
    wcel
    #
    @6
    @2
    cle
    wbr
    #
    @4
    @8
    cle
    wbr
    #
    @10
    wph
    @6
    wph
    @30
    cr
    cI
    cQ
    fourierdlem20.q
    wph
    @0
    @30
    cI
    @31
    @78
    sseldi
    #
    ffvelrnd
    rexrd
    wph
    @8
    wph
    @30
    cr
    @7
    cQ
    fourierdlem20.q
    wph
    @1
    @7
    @30
    wcel
    #
    @78
    cc0
    cM
    cI
    fzofzp1
    syl
    #
    ffvelrnd
    #
    rexrd
    #
    wph
    @1
    @80
    wph
    cI
    @20
    wcel
    @1
    @80
    wa
    wph
    cI
    @21
    @20
    fourierdlem20.i
    @77
    syl5eqel
    @19
    @80
    vk
    cI
    @0
    vk
    cI
    @21
    fourierdlem20.i
    vk
    @20
    cr
    clt
    @19
    vk
    @0
    nfrab1
    vk
    cr
    nfcv
    vk
    clt
    nfcv
    nfsup
    nfcxfr
    #
    vk
    @0
    nfcv
    #
    vk
    @6
    @2
    cle
    vk
    cI
    cQ
    vk
    cQ
    nfcv
    #
    @87
    nffv
    vk
    cle
    nfcv
    #
    vk
    @2
    nfcv
    #
    nfbr
    @17
    cI
    wceq
    @18
    @6
    @2
    cle
    @17
    cI
    cQ
    fveq2
    breq1d
    elrabf
    sylib
    simprd
    wph
    @81
    cJ
    @25
    clt
    wbr
    #
    @25
    @3
    clt
    wbr
    #
    wa
    #
    vj
    cz
    wrex
    #
    wph
    @81
    wn
    #
    @8
    @4
    clt
    wbr
    #
    @95
    wph
    @96
    wa
    #
    @97
    @96
    wph
    @96
    simpr
    @98
    @79
    @4
    cxr
    wcel
    #
    @97
    @96
    wb
    wph
    @79
    @96
    @86
    adantr
    wph
    @99
    @96
    wph
    cT
    cxr
    @4
    wph
    cT
    @42
    cxr
    @57
    cA
    cB
    iccssxr
    syl6ss
    wph
    @60
    cT
    @3
    cS
    @64
    wph
    @65
    @3
    @60
    wcel
    #
    fourierdlem20.j
    cc0
    cN
    cJ
    fzofzp1
    syl
    #
    ffvelrnd
    #
    sseldd
    adantr
    @8
    @4
    xrltnle
    syl2anc
    mpbird
    @60
    cz
    wss
    wph
    @97
    wa
    #
    @94
    vj
    @60
    wrex
    #
    @95
    cc0
    cN
    fzssz
    @103
    @8
    @25
    cS
    cfv
    #
    wceq
    #
    vj
    @60
    wrex
    #
    @104
    @103
    @60
    cT
    cS
    wfo
    #
    @8
    cT
    wcel
    @107
    wph
    @108
    @97
    wph
    @61
    @62
    @108
    fourierdlem20.s
    @63
    @60
    cT
    cS
    f1ofo
    3syl
    adantr
    @103
    @8
    @47
    cT
    @103
    @8
    @46
    wcel
    @8
    @47
    wcel
    @103
    @44
    @45
    @8
    wph
    @8
    @44
    wcel
    #
    @97
    wph
    cQ
    wfun
    #
    @7
    cQ
    cdm
    #
    wcel
    @109
    wph
    @30
    cr
    cQ
    wf
    #
    @110
    fourierdlem20.q
    @30
    cr
    cQ
    ffun
    syl
    wph
    @7
    @30
    @111
    @84
    wph
    @111
    @30
    wph
    @112
    @111
    @30
    wceq
    fourierdlem20.q
    @30
    cr
    cQ
    fdm
    syl
    eqcomd
    eleqtrd
    @7
    cQ
    fvelrn
    syl2anc
    adantr
    @103
    cA
    cB
    @8
    wph
    @52
    @97
    @55
    adantr
    wph
    @53
    @97
    @56
    adantr
    wph
    @8
    cr
    wcel
    #
    @97
    @85
    adantr
    #
    wph
    cA
    @8
    clt
    wbr
    @97
    wph
    cA
    @2
    @8
    fourierdlem20.a
    wph
    @42
    cr
    @2
    @58
    @69
    sseldd
    #
    @85
    @70
    wph
    @113
    @2
    @8
    clt
    wbr
    #
    @85
    wph
    @113
    wa
    #
    @116
    cI
    @7
    clt
    wbr
    #
    wph
    @116
    wn
    #
    @118
    @113
    wph
    @119
    wa
    cI
    wph
    cI
    cr
    wcel
    #
    @119
    wph
    cI
    @30
    wcel
    cI
    cz
    wcel
    @120
    @82
    @30
    cz
    cI
    @32
    sseli
    cI
    zre
    3syl
    #
    adantr
    ltp1d
    adantlr
    @117
    @119
    @8
    @2
    cle
    wbr
    #
    @118
    wn
    #
    @117
    @119
    wa
    @8
    @2
    wph
    @113
    @119
    simplr
    wph
    @2
    cr
    wcel
    #
    @113
    @119
    @115
    ad2antrr
    @117
    @119
    simpr
    nltled
    wph
    @122
    @123
    @113
    wph
    @122
    wa
    #
    @7
    cI
    @125
    cI
    c1
    wph
    @120
    @122
    @121
    adantr
    #
    @125
    1red
    readdcld
    @126
    @125
    @7
    @21
    cI
    cle
    @125
    @20
    cr
    wss
    #
    @24
    @29
    @7
    @20
    wcel
    #
    @7
    @21
    cle
    wbr
    @127
    @125
    @20
    @0
    cr
    @22
    vj
    @0
    cr
    @75
    @25
    @25
    cc0
    cM
    elfzoelz
    zred
    ssriv
    sstri
    a1i
    wph
    @24
    @122
    @71
    adantr
    wph
    @29
    @122
    @76
    adantr
    @125
    @7
    @0
    wcel
    #
    @122
    @128
    @125
    @129
    @8
    cB
    clt
    wbr
    #
    @125
    @130
    @129
    wn
    #
    @125
    @8
    @2
    cB
    wph
    @113
    @122
    @85
    adantr
    wph
    @124
    @122
    @115
    adantr
    #
    wph
    cB
    cr
    wcel
    #
    @122
    fourierdlem20.b
    adantr
    #
    wph
    @122
    simpr
    #
    @125
    @2
    @4
    cB
    @132
    wph
    @4
    cr
    wcel
    #
    @122
    wph
    cT
    cr
    @4
    @59
    @102
    sseldd
    #
    adantr
    @134
    wph
    @2
    @4
    clt
    wbr
    #
    @122
    wph
    cJ
    @3
    clt
    wbr
    #
    @138
    wph
    cJ
    wph
    @65
    cJ
    cz
    wcel
    #
    cJ
    cr
    wcel
    fourierdlem20.j
    cJ
    cc0
    cN
    elfzoelz
    #
    cJ
    zre
    3syl
    ltp1d
    wph
    @61
    @66
    @100
    @139
    @138
    wb
    fourierdlem20.s
    @67
    @101
    @60
    cT
    cJ
    @3
    clt
    clt
    cS
    isorel
    syl12anc
    mpbid
    adantr
    wph
    @4
    cB
    cle
    wbr
    #
    @122
    wph
    @52
    @53
    @4
    @42
    wcel
    @142
    @55
    @56
    wph
    cT
    @42
    @4
    @57
    @102
    sseldd
    cA
    cB
    @4
    iccleub
    syl3anc
    #
    adantr
    ltletrd
    lelttrd
    adantr
    wph
    @131
    @130
    wn
    @122
    wph
    @131
    wa
    #
    cB
    @8
    wph
    @133
    @131
    fourierdlem20.b
    adantr
    wph
    @113
    @131
    @85
    adantr
    @144
    cB
    cM
    cQ
    cfv
    #
    @8
    cle
    wph
    cB
    @145
    cle
    wbr
    @131
    fourierdlem20.qm
    adantr
    @144
    cM
    @7
    cQ
    @144
    @7
    cM
    @144
    @7
    cM
    cM
    cfz
    co
    #
    wcel
    @7
    cM
    wceq
    @144
    @7
    cM
    cM
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @146
    @144
    @38
    @7
    cc0
    @147
    cfzo
    co
    #
    wcel
    #
    @131
    wa
    @7
    @148
    wcel
    wph
    @38
    @131
    @40
    adantr
    @144
    @150
    @131
    @144
    @7
    @30
    @149
    wph
    @83
    @131
    @84
    adantr
    wph
    @30
    @149
    wceq
    #
    @131
    wph
    @38
    @151
    @40
    cc0
    cM
    fzval3
    syl
    adantr
    eleqtrd
    wph
    @131
    simpr
    jca
    @147
    @7
    cc0
    cM
    elfzonelfzo
    sylc
    wph
    @148
    @146
    wceq
    @131
    wph
    @146
    @148
    wph
    @38
    @146
    @148
    wceq
    @40
    cM
    cM
    fzval3
    syl
    eqcomd
    adantr
    eleqtrd
    @7
    cM
    elfz1eq
    syl
    eqcomd
    fveq2d
    breqtrd
    lensymd
    adantlr
    condan
    @135
    @19
    @122
    vk
    @7
    @0
    vk
    cI
    c1
    caddc
    @87
    vk
    caddc
    nfcv
    vk
    c1
    nfcv
    nfov
    #
    @88
    vk
    @8
    @2
    cle
    vk
    @7
    cQ
    @89
    @152
    nffv
    @90
    @91
    nfbr
    @17
    @7
    wceq
    @18
    @8
    @2
    cle
    @17
    @7
    cQ
    fveq2
    breq1d
    elrabf
    sylanbrc
    vx
    vj
    @20
    @7
    suprub
    syl31anc
    fourierdlem20.i
    syl6breqr
    lensymd
    adantlr
    syldan
    condan
    mpdan
    #
    lelttrd
    adantr
    @103
    @8
    @4
    cB
    @114
    wph
    @136
    @97
    @137
    adantr
    wph
    @133
    @97
    fourierdlem20.b
    adantr
    wph
    @97
    simpr
    wph
    @142
    @97
    @143
    adantr
    ltletrd
    eliood
    elind
    @8
    @46
    @43
    elun2
    syl
    fourierdlem20.t
    syl6eleqr
    vj
    @60
    cT
    @8
    cS
    foelrn
    syl2anc
    @103
    @106
    @94
    vj
    @60
    @103
    @25
    @60
    wcel
    #
    wa
    #
    @106
    @94
    @155
    @106
    wa
    #
    @92
    @93
    wph
    @154
    @106
    @92
    @97
    wph
    @154
    wa
    #
    @106
    wa
    #
    @92
    @2
    @105
    clt
    wbr
    #
    wph
    @106
    @159
    @154
    wph
    @106
    wa
    @2
    @8
    @105
    clt
    wph
    @116
    @106
    @153
    adantr
    wph
    @106
    simpr
    breqtrd
    adantlr
    @158
    @61
    @66
    @154
    wa
    #
    @92
    @159
    wb
    wph
    @61
    @154
    @106
    fourierdlem20.s
    ad2antrr
    @157
    @160
    @106
    wph
    @66
    @154
    @67
    anim1i
    adantr
    @60
    cT
    cJ
    @25
    clt
    clt
    cS
    isorel
    syl2anc
    mpbird
    adantllr
    @156
    @93
    @105
    @4
    clt
    wbr
    #
    @103
    @106
    @161
    @154
    @97
    @106
    @161
    wph
    @97
    @106
    wa
    @105
    @8
    @4
    clt
    @106
    @105
    @8
    wceq
    #
    @97
    @106
    @162
    @8
    @105
    eqcom
    biimpi
    adantl
    @97
    @106
    simpl
    eqbrtrd
    adantll
    adantlr
    @155
    @93
    @161
    wb
    #
    @106
    @155
    @61
    @154
    @100
    @163
    wph
    @61
    @97
    @154
    fourierdlem20.s
    ad2antrr
    @103
    @154
    simpr
    wph
    @100
    @97
    @154
    @101
    ad2antrr
    @60
    cT
    @25
    @3
    clt
    clt
    cS
    isorel
    syl12anc
    adantr
    mpbird
    jca
    ex
    reximdva
    mpd
    @94
    vj
    @60
    cz
    ssrexv
    mpsyl
    syldan
    wph
    @95
    wn
    @96
    wph
    @94
    vj
    cz
    wph
    @25
    cz
    wcel
    #
    wa
    #
    @94
    @164
    wph
    @164
    @94
    simplr
    @165
    @94
    wa
    @140
    @92
    @93
    @164
    wn
    wph
    @140
    @164
    @94
    wph
    @65
    @140
    fourierdlem20.j
    @141
    syl
    ad2antrr
    @165
    @92
    @93
    simprl
    @165
    @92
    @93
    simprr
    cJ
    @25
    btwnnz
    syl3anc
    pm2.65da
    nrexdv
    adantr
    condan
    @6
    @8
    @2
    @4
    ioossioo
    syl22anc
    @16
    @10
    vi
    cI
    @0
    @11
    cI
    wceq
    #
    @15
    @9
    @5
    @166
    @12
    @6
    @14
    @8
    cioo
    @11
    cI
    cQ
    fveq2
    @166
    @13
    @7
    cQ
    @11
    cI
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    sseq2d
    rspcev
    syl2anc
end
