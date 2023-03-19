include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cn0.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cc.mm"
include "caddc.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "cmap.mm"
include "cun.mm"
include "wf.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wa.mm"
include "subcl.mm"
include "adantl.mm"
include "cnex.mm"
include "nn0ex.mm"
include "elmap.mm"
include "sylib.mm"
include "inidm.mm"
include "off.mm"
include "sylibr.mm"
include "0cn.mm"
include "snssi.mm"
include "ax-mp.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "oveq1i.mm"
include "syl6eleqr.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "cima.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "clt.mm"
include "cr.mm"
include "wb.mm"
include "nn0red.mm"
include "nn0re.mm"
include "ltnle.mm"
include "syl2an.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "eqidd.mm"
include "ofval.mm"
include "adantrr.mm"
include "adantr.mm"
include "nn0cnd.mm"
include "addcomd.mm"
include "cz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nn0zd.mm"
include "eluzadd.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "addid2d.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "eluzle.mm"
include "simprr.mm"
include "lelttrd.mm"
include "ltnled.mm"
include "mpbid.mm"
include "plyco0.mm"
include "r19.21bi.mm"
include "necon1bd.mm"
include "mpd.mm"
include "oveq12d.mm"
include "0m0e0.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "expr.mm"
include "sylbird.mm"
include "necon1ad.mm"
include "ralrimiva.mm"
include "mpbird.mm"
include "c0p.mm"
include "cmpt.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "df-0p.mm"
include "fconstmpt.mm"
include "eqtri.mm"
include "elfznn0.mm"
include "adantlr.mm"
include "oveq1d.mm"
include "ffvelrnda.mm"
include "expcl.mm"
include "adantll.mm"
include "subdird.mm"
include "sylan2.mm"
include "sumeq2dv.mm"
include "fzfid.mm"
include "mulcld.mm"
include "fsumsub.mm"
include "fsumcl.mm"
include "eqtr3d.mm"
include "fveq1d.mm"
include "simpr.mm"
include "sumex.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "fzss2.mm"
include "sselda.mm"
include "syldan.mm"
include "cdif.mm"
include "eldifn.mm"
include "eldifi.mm"
include "elfz5.mm"
include "sylibrd.mm"
include "mul02d.mm"
include "fsumss.mm"
include "3eqtr3d.mm"
include "subeq0bd.mm"
include "3eqtrrd.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "plyeq0.mm"
include "ofsubeq0.mm"
include "syl3anc.mm"

theorem coeeulem
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  assume coeeu.1: |- ( ph -> F e. ( Poly ` S ) )
  assume coeeu.2: |- ( ph -> A e. ( CC ^m NN0 ) )
  assume coeeu.3: |- ( ph -> B e. ( CC ^m NN0 ) )
  assume coeeu.4: |- ( ph -> M e. NN0 )
  assume coeeu.5: |- ( ph -> N e. NN0 )
  assume coeeu.6: |- ( ph -> ( A " ( ZZ>= ` ( M + 1 ) ) ) = { 0 } )
  assume coeeu.7: |- ( ph -> ( B " ( ZZ>= ` ( N + 1 ) ) ) = { 0 } )
  assume coeeu.8: |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... M ) ( ( A ` k ) x. ( z ^ k ) ) ) )
  assume coeeu.9: |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( B ` k ) x. ( z ^ k ) ) ) )

  disjoint k z
  disjoint B k
  disjoint B z
  disjoint k ph
  disjoint ph z
  disjoint A k
  disjoint A z
  disjoint M k
  disjoint M z
  disjoint N k
  disjoint N z
  disjoint k y
  disjoint y z
  disjoint B y
  disjoint a b
  disjoint a f
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a w
  disjoint F a
  disjoint b f
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b w
  disjoint F b
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f w
  disjoint F f
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint F j
  disjoint m n
  disjoint m w
  disjoint F m
  disjoint n w
  disjoint F n
  disjoint F w
  disjoint k x
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint S a
  disjoint S b
  disjoint S j
  disjoint S m
  disjoint S n
  disjoint S w
  disjoint a k
  disjoint a z
  disjoint b k
  disjoint b z
  disjoint f k
  disjoint f z
  disjoint j k
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k w
  disjoint m z
  disjoint n z
  disjoint w z
  disjoint A x
  disjoint A y
  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cB
    cmin
    cof
    co
    #
    cn0
    cc0
    csn
    #
    cxp
    wceq
    #
    cA
    cB
    wceq
    #
    wph
    vz
    @0
    cc
    vk
    cM
    cN
    caddc
    co
    #
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    wph
    cM
    cN
    coeeu.4
    coeeu.5
    nn0addcld
    #
    wph
    @0
    cc
    cn0
    cmap
    co
    #
    cc
    @1
    cun
    #
    cn0
    cmap
    co
    wph
    cn0
    cc
    @0
    wf
    #
    @0
    @6
    wcel
    wph
    vx
    vy
    cn0
    cn0
    cn0
    cmin
    cc
    cc
    cc
    cA
    cB
    cvv
    cvv
    vx
    cv
    #
    cc
    wcel
    vy
    cv
    #
    cc
    wcel
    wa
    @9
    @10
    cmin
    co
    cc
    wcel
    wph
    @9
    @10
    subcl
    adantl
    wph
    cA
    @6
    wcel
    cn0
    cc
    cA
    wf
    #
    coeeu.2
    cc
    cn0
    cA
    cnex
    nn0ex
    elmap
    sylib
    #
    wph
    cB
    @6
    wcel
    cn0
    cc
    cB
    wf
    #
    coeeu.3
    cc
    cn0
    cB
    cnex
    nn0ex
    elmap
    sylib
    #
    cn0
    cvv
    wcel
    #
    wph
    nn0ex
    a1i
    #
    @16
    cn0
    inidm
    #
    off
    #
    cc
    cn0
    @0
    cnex
    nn0ex
    elmap
    sylibr
    @7
    cc
    cn0
    cmap
    @1
    cc
    wss
    #
    @7
    cc
    wceq
    cc0
    cc
    wcel
    @19
    0cn
    cc0
    cc
    snssi
    ax-mp
    @1
    cc
    ssequn2
    mpbi
    oveq1i
    syl6eleqr
    wph
    @0
    @4
    c1
    caddc
    co
    cuz
    cfv
    cima
    @1
    wceq
    #
    vk
    cv
    #
    @0
    cfv
    #
    cc0
    wne
    @21
    @4
    cle
    wbr
    #
    wi
    #
    vk
    cn0
    wral
    #
    wph
    @24
    vk
    cn0
    wph
    @21
    cn0
    wcel
    #
    wa
    #
    @23
    @22
    cc0
    @27
    @23
    wn
    #
    @4
    @21
    clt
    wbr
    #
    @22
    cc0
    wceq
    #
    wph
    @4
    cr
    wcel
    #
    @21
    cr
    wcel
    #
    @29
    @28
    wb
    @26
    wph
    @4
    @5
    nn0red
    #
    @21
    nn0re
    #
    @4
    @21
    ltnle
    syl2an
    wph
    @26
    @29
    @30
    wph
    @26
    @29
    wa
    #
    wa
    #
    @22
    @21
    cA
    cfv
    #
    @21
    cB
    cfv
    #
    cmin
    co
    #
    cc0
    wph
    @26
    @22
    @39
    wceq
    #
    @29
    wph
    cn0
    cn0
    @37
    @38
    cmin
    cn0
    cA
    cB
    cvv
    cvv
    @21
    wph
    @11
    cA
    cn0
    wfn
    @12
    cn0
    cc
    cA
    ffn
    syl
    wph
    @13
    cB
    cn0
    wfn
    @14
    cn0
    cc
    cB
    ffn
    syl
    @16
    @16
    @17
    @27
    @37
    eqidd
    @27
    @38
    eqidd
    ofval
    #
    adantrr
    @36
    @39
    cc0
    cc0
    cmin
    co
    cc0
    @36
    @37
    cc0
    @38
    cc0
    cmin
    @36
    @21
    cM
    cle
    wbr
    #
    wn
    #
    @37
    cc0
    wceq
    #
    @36
    cM
    @21
    clt
    wbr
    @43
    @36
    cM
    @4
    @21
    wph
    cM
    cr
    wcel
    @35
    wph
    cM
    coeeu.4
    nn0red
    adantr
    #
    wph
    @31
    @35
    @33
    adantr
    #
    wph
    @26
    @32
    @29
    @26
    @32
    wph
    @34
    adantl
    adantrr
    #
    wph
    cM
    @4
    cle
    wbr
    #
    @35
    wph
    @4
    cM
    cuz
    cfv
    #
    wcel
    #
    @48
    wph
    @4
    cc0
    cM
    caddc
    co
    #
    cuz
    cfv
    #
    @49
    wph
    @4
    cN
    cM
    caddc
    co
    #
    @52
    wph
    cM
    cN
    wph
    cM
    coeeu.4
    nn0cnd
    #
    wph
    cN
    coeeu.5
    nn0cnd
    #
    addcomd
    wph
    cN
    cc0
    cuz
    cfv
    #
    wcel
    cM
    cz
    wcel
    #
    @53
    @52
    wcel
    wph
    cN
    cn0
    @56
    coeeu.5
    nn0uz
    syl6eleq
    wph
    cM
    coeeu.4
    nn0zd
    #
    cM
    cc0
    cN
    eluzadd
    syl2anc
    eqeltrd
    wph
    @51
    cM
    cuz
    wph
    cM
    @54
    addid2d
    fveq2d
    eleqtrd
    #
    cM
    @4
    eluzle
    syl
    adantr
    wph
    @26
    @29
    simprr
    #
    lelttrd
    @36
    cM
    @21
    @45
    @47
    ltnled
    mpbid
    @36
    @42
    @37
    cc0
    wph
    @26
    @37
    cc0
    wne
    #
    @42
    wi
    #
    @29
    wph
    @62
    vk
    cn0
    wph
    cA
    cM
    c1
    caddc
    co
    cuz
    cfv
    cima
    @1
    wceq
    #
    @62
    vk
    cn0
    wral
    #
    coeeu.6
    wph
    cM
    cn0
    wcel
    @11
    @63
    @64
    wb
    coeeu.4
    @12
    cA
    vk
    cM
    plyco0
    syl2anc
    mpbid
    r19.21bi
    #
    adantrr
    necon1bd
    mpd
    @36
    @21
    cN
    cle
    wbr
    #
    wn
    #
    @38
    cc0
    wceq
    #
    @36
    cN
    @21
    clt
    wbr
    @67
    @36
    cN
    @4
    @21
    wph
    cN
    cr
    wcel
    @35
    wph
    cN
    coeeu.5
    nn0red
    adantr
    #
    @46
    @47
    wph
    cN
    @4
    cle
    wbr
    #
    @35
    wph
    @4
    cN
    cuz
    cfv
    #
    wcel
    #
    @70
    wph
    @4
    cc0
    cN
    caddc
    co
    #
    cuz
    cfv
    #
    @71
    wph
    cM
    @56
    wcel
    cN
    cz
    wcel
    #
    @4
    @74
    wcel
    wph
    cM
    cn0
    @56
    coeeu.4
    nn0uz
    syl6eleq
    wph
    cN
    coeeu.5
    nn0zd
    #
    cN
    cc0
    cM
    eluzadd
    syl2anc
    wph
    @73
    cN
    cuz
    wph
    cN
    @55
    addid2d
    fveq2d
    eleqtrd
    #
    cN
    @4
    eluzle
    syl
    adantr
    @60
    lelttrd
    @36
    cN
    @21
    @69
    @47
    ltnled
    mpbid
    @36
    @66
    @38
    cc0
    wph
    @26
    @38
    cc0
    wne
    #
    @66
    wi
    #
    @29
    wph
    @79
    vk
    cn0
    wph
    cB
    cN
    c1
    caddc
    co
    cuz
    cfv
    cima
    @1
    wceq
    #
    @79
    vk
    cn0
    wral
    #
    coeeu.7
    wph
    cN
    cn0
    wcel
    @13
    @80
    @81
    wb
    coeeu.5
    @14
    cB
    vk
    cN
    plyco0
    syl2anc
    mpbid
    r19.21bi
    #
    adantrr
    necon1bd
    mpd
    oveq12d
    0m0e0
    syl6eq
    eqtrd
    expr
    sylbird
    necon1ad
    ralrimiva
    wph
    @4
    cn0
    wcel
    @8
    @20
    @25
    wb
    @5
    @18
    @0
    vk
    @4
    plyco0
    syl2anc
    mpbird
    wph
    c0p
    vz
    cc
    cc0
    cmpt
    #
    vz
    cc
    cc0
    @4
    cfz
    co
    #
    @22
    vz
    cv
    #
    @21
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    c0p
    cc
    @1
    cxp
    @83
    df-0p
    vz
    cc
    cc0
    fconstmpt
    eqtri
    wph
    vz
    cc
    cc0
    @88
    wph
    @85
    cc
    wcel
    #
    wa
    #
    @88
    @84
    @37
    @86
    cmul
    co
    #
    @38
    @86
    cmul
    co
    #
    cmin
    co
    #
    vk
    csu
    @84
    @91
    vk
    csu
    #
    @84
    @92
    vk
    csu
    #
    cmin
    co
    cc0
    @90
    @84
    @87
    @93
    vk
    @21
    @84
    wcel
    #
    @90
    @26
    @87
    @93
    wceq
    @21
    @4
    elfznn0
    #
    @90
    @26
    wa
    #
    @87
    @39
    @86
    cmul
    co
    @93
    @98
    @22
    @39
    @86
    cmul
    wph
    @26
    @40
    @89
    @41
    adantlr
    oveq1d
    @98
    @37
    @38
    @86
    @90
    cn0
    cc
    @21
    cA
    wph
    @11
    @89
    @12
    adantr
    ffvelrnda
    #
    @90
    cn0
    cc
    @21
    cB
    wph
    @13
    @89
    @14
    adantr
    ffvelrnda
    #
    @89
    @26
    @86
    cc
    wcel
    #
    wph
    @85
    @21
    expcl
    #
    adantll
    #
    subdird
    eqtrd
    sylan2
    sumeq2dv
    @90
    @84
    @91
    @92
    vk
    @90
    cc0
    @4
    fzfid
    #
    @96
    @90
    @26
    @91
    cc
    wcel
    #
    @97
    @98
    @37
    @86
    @99
    @103
    mulcld
    sylan2
    #
    @96
    @90
    @26
    @92
    cc
    wcel
    #
    @97
    @98
    @38
    @86
    @100
    @103
    mulcld
    sylan2
    #
    fsumsub
    @90
    @94
    @95
    @90
    @84
    @91
    vk
    @104
    @106
    fsumcl
    @90
    @85
    vz
    cc
    cc0
    cM
    cfz
    co
    #
    @91
    vk
    csu
    #
    cmpt
    #
    cfv
    #
    @85
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    @92
    vk
    csu
    #
    cmpt
    #
    cfv
    #
    @94
    @95
    wph
    @112
    @116
    wceq
    @89
    wph
    @85
    @111
    @115
    wph
    cF
    @111
    @115
    coeeu.8
    coeeu.9
    eqtr3d
    fveq1d
    adantr
    @90
    @112
    @110
    @94
    @90
    @89
    @110
    cvv
    wcel
    @112
    @110
    wceq
    wph
    @89
    simpr
    #
    @109
    @91
    vk
    sumex
    vz
    cc
    @110
    cvv
    @111
    @111
    eqid
    fvmpt2
    sylancl
    @90
    @109
    @84
    @91
    vk
    wph
    @109
    @84
    wss
    #
    @89
    wph
    @50
    @118
    @59
    cM
    cc0
    @4
    fzss2
    syl
    adantr
    #
    @90
    @21
    @109
    wcel
    #
    @96
    @105
    @90
    @109
    @84
    @21
    @119
    sselda
    @106
    syldan
    @90
    @21
    @84
    @109
    cdif
    wcel
    #
    wa
    #
    @91
    cc0
    @86
    cmul
    co
    #
    cc0
    @122
    @37
    cc0
    @86
    cmul
    @122
    @120
    wn
    #
    @44
    @121
    @124
    @90
    @21
    @84
    @109
    eldifn
    adantl
    @121
    @90
    @26
    @124
    @44
    wi
    @121
    @96
    @26
    @21
    @84
    @109
    eldifi
    @97
    syl
    #
    @98
    @120
    @37
    cc0
    wph
    @26
    @61
    @120
    wi
    @89
    @27
    @61
    @42
    @120
    @65
    @27
    @21
    @56
    wcel
    #
    @57
    @120
    @42
    wb
    @27
    @21
    cn0
    @56
    wph
    @26
    simpr
    nn0uz
    syl6eleq
    #
    wph
    @57
    @26
    @58
    adantr
    @21
    cc0
    cM
    elfz5
    syl2anc
    sylibrd
    adantlr
    necon1bd
    sylan2
    mpd
    oveq1d
    @122
    @86
    @90
    @89
    @26
    @101
    @121
    @117
    @125
    @102
    syl2an
    mul02d
    eqtrd
    @104
    fsumss
    eqtrd
    @90
    @116
    @114
    @95
    @90
    @89
    @114
    cvv
    wcel
    @116
    @114
    wceq
    @117
    @113
    @92
    vk
    sumex
    vz
    cc
    @114
    cvv
    @115
    @115
    eqid
    fvmpt2
    sylancl
    @90
    @113
    @84
    @92
    vk
    wph
    @113
    @84
    wss
    #
    @89
    wph
    @72
    @128
    @77
    cN
    cc0
    @4
    fzss2
    syl
    adantr
    #
    @90
    @21
    @113
    wcel
    #
    @96
    @107
    @90
    @113
    @84
    @21
    @129
    sselda
    @108
    syldan
    @90
    @21
    @84
    @113
    cdif
    wcel
    #
    wa
    #
    @92
    @123
    cc0
    @132
    @38
    cc0
    @86
    cmul
    @132
    @130
    wn
    #
    @68
    @131
    @133
    @90
    @21
    @84
    @113
    eldifn
    adantl
    @131
    @90
    @26
    @133
    @68
    wi
    @131
    @96
    @26
    @21
    @84
    @113
    eldifi
    @97
    syl
    #
    @98
    @130
    @38
    cc0
    wph
    @26
    @78
    @130
    wi
    @89
    @27
    @78
    @66
    @130
    @82
    @27
    @126
    @75
    @130
    @66
    wb
    @127
    wph
    @75
    @26
    @76
    adantr
    @21
    cc0
    cN
    elfz5
    syl2anc
    sylibrd
    adantlr
    necon1bd
    sylan2
    mpd
    oveq1d
    @132
    @86
    @90
    @89
    @26
    @101
    @131
    @117
    @134
    @102
    syl2an
    mul02d
    eqtrd
    @104
    fsumss
    eqtrd
    3eqtr3d
    subeq0bd
    3eqtrrd
    mpteq2dva
    syl5eq
    plyeq0
    wph
    @15
    @11
    @13
    @2
    @3
    wb
    @16
    @12
    @14
    cn0
    cA
    cB
    cvv
    ofsubeq0
    syl3anc
    mpbid
end
