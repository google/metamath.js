include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cabs.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cn0.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "weq.mm"
include "oveq2.mm"
include "adantl.mm"
include "nnnn0.mm"
include "rpcnd.mm"
include "adantr.mm"
include "expcld.mm"
include "fvmptd.mm"
include "cli.mm"
include "cneg.mm"
include "1red.mm"
include "renegcld.mm"
include "0red.mm"
include "rpred.mm"
include "neg1lt0.mm"
include "rpgt0d.mm"
include "lttrd.mm"
include "absltd.mm"
include "mpbir2and.mm"
include "expcnv.mm"
include "syl5eqbr.mm"
include "climi.mm"
include "r19.26.mm"
include "simprbi.mm"
include "ad2antlr.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspccva.mm"
include "sylancom.mm"
include "cr.mm"
include "wb.mm"
include "crp.mm"
include "simplll.mm"
include "syl.mm"
include "simpllr.mm"
include "eluznn0.mm"
include "reexpcld.mm"
include "rpre.mm"
include "3syl.mm"
include "recn.mm"
include "subid1d.mm"
include "abslt.mm"
include "bitrd.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simprd.mm"
include "eluznn.mm"
include "ltsub2d.mm"
include "ralrimiva.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "recnd.mm"
include "0lt1.mm"
include "gt0ne0d.mm"
include "reccld.mm"
include "rereccld.mm"
include "recgt0d.mm"
include "ltdiv23.mm"
include "syl122anc.mm"
include "1cnd.mm"
include "div1d.mm"
include "mpbird.mm"
include "climi2.mm"
include "wi.mm"
include "simpll.mm"
include "wss.mm"
include "uznnssnn.mm"
include "simpr.mm"
include "sseldd.mm"
include "cle.mm"
include "ltled.mm"
include "expge0d.mm"
include "absidd.mm"
include "eqtrd.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "rexanuz2.mm"
include "sylanbrc.mm"
include "cz.mm"
include "nnz.mm"
include "uzid.mm"
include "anbi12d.mm"
include "wne.mm"
include "jca.mm"
include "expdiv.mm"
include "syl3anc.mm"
include "1exp.mm"
include "anbi2d.mm"

theorem stoweidlem7
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem7.1: |- F = ( i e. NN0 |-> ( ( 1 / A ) ^ i ) )
  assume stoweidlem7.2: |- G = ( i e. NN0 |-> ( B ^ i ) )
  assume stoweidlem7.3: |- ( ph -> A e. RR )
  assume stoweidlem7.4: |- ( ph -> 1 < A )
  assume stoweidlem7.5: |- ( ph -> B e. RR+ )
  assume stoweidlem7.6: |- ( ph -> B < 1 )
  assume stoweidlem7.7: |- ( ph -> E e. RR+ )

  disjoint i n
  disjoint A i
  disjoint A n
  disjoint B i
  disjoint B n
  disjoint E i
  disjoint E n
  disjoint i ph
  disjoint n ph
  disjoint F n
  disjoint G n
  disjoint i k
  disjoint k n
  disjoint A k
  disjoint B k
  disjoint E k
  disjoint k ph
  disjoint F k
  disjoint G k
  disjoint k x
  assert |- ( ph -> E. n e. NN ( ( 1 - E ) < ( 1 - ( B ^ n ) ) /\ ( 1 / ( A ^ n ) ) < E ) )

  proof
    wph
    c1
    cE
    cmin
    co
    #
    c1
    cB
    vk
    cv
    #
    cexp
    co
    #
    cmin
    co
    #
    clt
    wbr
    #
    c1
    cA
    cdiv
    co
    #
    @1
    cexp
    co
    #
    cE
    clt
    wbr
    #
    wa
    #
    vk
    vn
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vn
    cn
    wrex
    #
    @0
    c1
    cB
    @9
    cexp
    co
    #
    cmin
    co
    #
    clt
    wbr
    #
    c1
    cA
    @9
    cexp
    co
    #
    cdiv
    co
    #
    cE
    clt
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    wph
    @4
    vk
    @10
    wral
    #
    vn
    cn
    wrex
    #
    @7
    vk
    @10
    wral
    #
    vn
    cn
    wrex
    #
    @12
    wph
    @2
    cc
    wcel
    #
    @2
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    wa
    vk
    @10
    wral
    #
    vn
    cn
    wrex
    @21
    wph
    cc0
    @2
    cE
    vn
    vk
    cG
    c1
    cn
    nnuz
    wph
    1zzd
    #
    stoweidlem7.7
    wph
    @1
    cn
    wcel
    #
    wa
    #
    vi
    @1
    cB
    vi
    cv
    #
    cexp
    co
    #
    @2
    cn0
    cG
    cc
    cG
    vi
    cn0
    @33
    cmpt
    #
    wceq
    @31
    stoweidlem7.2
    a1i
    vi
    vk
    weq
    #
    @33
    @2
    wceq
    @31
    @32
    @1
    cB
    cexp
    oveq2
    adantl
    @30
    @1
    cn0
    wcel
    wph
    @1
    nnnn0
    adantl
    #
    @31
    cB
    @1
    wph
    cB
    cc
    wcel
    @30
    wph
    cB
    stoweidlem7.5
    rpcnd
    #
    adantr
    @36
    expcld
    fvmptd
    wph
    cG
    @34
    cc0
    cli
    stoweidlem7.2
    wph
    cB
    vi
    @37
    wph
    cB
    cabs
    cfv
    c1
    clt
    wbr
    c1
    cneg
    #
    cB
    clt
    wbr
    cB
    c1
    clt
    wbr
    wph
    @38
    cc0
    cB
    wph
    c1
    wph
    1red
    #
    renegcld
    #
    wph
    0red
    #
    wph
    cB
    stoweidlem7.5
    rpred
    #
    @38
    cc0
    clt
    wbr
    wph
    neg1lt0
    a1i
    #
    wph
    cB
    stoweidlem7.5
    rpgt0d
    lttrd
    stoweidlem7.6
    wph
    cB
    c1
    @42
    @39
    absltd
    mpbir2and
    expcnv
    syl5eqbr
    climi
    wph
    @28
    @20
    vn
    cn
    wph
    @9
    cn
    wcel
    #
    wa
    #
    @28
    @20
    @45
    @28
    wa
    #
    @0
    c1
    @33
    cmin
    co
    #
    clt
    wbr
    #
    vi
    @10
    wral
    @20
    @46
    @48
    vi
    @10
    @46
    @32
    @10
    wcel
    #
    wa
    #
    @33
    cE
    clt
    wbr
    #
    @48
    @50
    cE
    cneg
    @33
    clt
    wbr
    #
    @51
    @50
    @33
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    @52
    @51
    wa
    #
    @46
    @49
    @27
    vk
    @10
    wral
    #
    @55
    @28
    @57
    @45
    @49
    @28
    @24
    vk
    @10
    wral
    @57
    @24
    @27
    vk
    @10
    r19.26
    simprbi
    ad2antlr
    @27
    @55
    vk
    @32
    @10
    vk
    vi
    weq
    #
    @26
    @54
    cE
    clt
    @58
    @25
    @53
    cabs
    @58
    @2
    @33
    cc0
    cmin
    @1
    @32
    cB
    cexp
    oveq2
    #
    oveq1d
    fveq2d
    breq1d
    rspccva
    sylancom
    @50
    @33
    cr
    wcel
    #
    cE
    cr
    wcel
    #
    @55
    @56
    wb
    @50
    cB
    @32
    @50
    cB
    @50
    wph
    cB
    crp
    wcel
    wph
    @44
    @28
    @49
    simplll
    #
    stoweidlem7.5
    syl
    rpred
    @46
    @49
    @9
    cn0
    wcel
    #
    @32
    cn0
    wcel
    #
    @50
    @44
    @63
    wph
    @44
    @28
    @49
    simpllr
    #
    @9
    nnnn0
    #
    syl
    @32
    @9
    eluznn0
    sylancom
    reexpcld
    @50
    wph
    cE
    crp
    wcel
    @61
    @62
    stoweidlem7.7
    cE
    rpre
    3syl
    @60
    @61
    wa
    #
    @55
    @33
    cabs
    cfv
    #
    cE
    clt
    wbr
    @56
    @67
    @54
    @68
    cE
    clt
    @67
    @53
    @33
    cabs
    @60
    @53
    @33
    wceq
    @61
    @60
    @33
    @33
    recn
    subid1d
    adantr
    fveq2d
    breq1d
    @33
    cE
    abslt
    bitrd
    syl2anc
    mpbid
    simprd
    @50
    wph
    @32
    cn
    wcel
    #
    @51
    @48
    wb
    @62
    @46
    @49
    @44
    @69
    @65
    @32
    @9
    eluznn
    sylancom
    wph
    @69
    wa
    #
    @33
    cE
    c1
    @70
    cB
    @32
    wph
    cB
    cr
    wcel
    @69
    @42
    adantr
    @69
    @64
    wph
    @32
    nnnn0
    adantl
    reexpcld
    wph
    @61
    @69
    wph
    cE
    stoweidlem7.7
    rpred
    adantr
    @70
    1red
    ltsub2d
    syl2anc
    mpbid
    ralrimiva
    @4
    @48
    vk
    vi
    @10
    @58
    @3
    @47
    @0
    clt
    @58
    @2
    @33
    c1
    cmin
    @59
    oveq2d
    breq2d
    cbvralv
    sylibr
    ex
    reximdva
    mpd
    wph
    @6
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    vk
    @10
    wral
    #
    vn
    cn
    wrex
    @23
    wph
    cc0
    @6
    cE
    vn
    vk
    cF
    c1
    cn
    nnuz
    @29
    stoweidlem7.7
    @31
    vi
    @1
    @5
    @32
    cexp
    co
    #
    @6
    cn0
    cF
    cc
    cF
    vi
    cn0
    @75
    cmpt
    #
    wceq
    @31
    stoweidlem7.1
    a1i
    @35
    @75
    @6
    wceq
    @31
    @32
    @1
    @5
    cexp
    oveq2
    adantl
    @36
    @31
    @5
    @1
    wph
    @5
    cc
    wcel
    @30
    wph
    cA
    wph
    cA
    stoweidlem7.3
    recnd
    #
    wph
    cA
    wph
    cc0
    c1
    cA
    @41
    @39
    stoweidlem7.3
    cc0
    c1
    clt
    wbr
    #
    wph
    0lt1
    a1i
    #
    stoweidlem7.4
    lttrd
    #
    gt0ne0d
    #
    reccld
    #
    adantr
    @36
    expcld
    #
    fvmptd
    wph
    cF
    @76
    cc0
    cli
    stoweidlem7.1
    wph
    @5
    vi
    @82
    wph
    @5
    cabs
    cfv
    c1
    clt
    wbr
    @38
    @5
    clt
    wbr
    @5
    c1
    clt
    wbr
    #
    wph
    @38
    cc0
    @5
    @40
    @41
    wph
    cA
    stoweidlem7.3
    @81
    rereccld
    #
    @43
    wph
    cA
    stoweidlem7.3
    @80
    recgt0d
    #
    lttrd
    wph
    @84
    c1
    cA
    clt
    wbr
    #
    stoweidlem7.4
    wph
    @84
    c1
    c1
    cdiv
    co
    #
    cA
    clt
    wbr
    #
    @87
    wph
    c1
    cr
    wcel
    #
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    @90
    @78
    @84
    @89
    wb
    @39
    stoweidlem7.3
    @80
    @39
    @79
    c1
    cA
    c1
    ltdiv23
    syl122anc
    wph
    @88
    c1
    cA
    clt
    wph
    c1
    wph
    1cnd
    div1d
    breq1d
    bitrd
    mpbird
    wph
    @5
    c1
    @85
    @39
    absltd
    mpbir2and
    expcnv
    syl5eqbr
    climi2
    wph
    @74
    @22
    vn
    cn
    @45
    @73
    @7
    vk
    @10
    @45
    @1
    @10
    wcel
    #
    wa
    #
    wph
    @30
    @73
    @7
    wi
    wph
    @44
    @91
    simpll
    @92
    @10
    cn
    @1
    @44
    @10
    cn
    wss
    wph
    @91
    @9
    uznnssnn
    ad2antlr
    @45
    @91
    simpr
    sseldd
    @31
    @73
    @7
    @31
    @72
    @6
    cE
    clt
    @31
    @72
    @6
    cabs
    cfv
    @6
    @31
    @71
    @6
    cabs
    @31
    @6
    @83
    subid1d
    fveq2d
    @31
    @6
    @31
    @5
    @1
    wph
    @5
    cr
    wcel
    @30
    @85
    adantr
    #
    @36
    reexpcld
    @31
    @5
    @1
    @93
    @36
    wph
    cc0
    @5
    cle
    wbr
    @30
    wph
    cc0
    @5
    @41
    @85
    @86
    ltled
    adantr
    expge0d
    absidd
    eqtrd
    breq1d
    biimpd
    syl2anc
    ralimdva
    reximdva
    mpd
    @4
    @7
    vn
    vk
    c1
    cn
    nnuz
    rexanuz2
    sylanbrc
    wph
    @11
    @19
    vn
    cn
    @45
    @11
    @19
    @45
    @11
    wa
    #
    @15
    @5
    @9
    cexp
    co
    #
    cE
    clt
    wbr
    #
    wa
    #
    @19
    @94
    @11
    @9
    @10
    wcel
    #
    @97
    @45
    @11
    simpr
    @44
    @98
    wph
    @11
    @44
    @9
    cz
    wcel
    #
    @98
    @9
    nnz
    #
    @9
    uzid
    syl
    ad2antlr
    @8
    @97
    vk
    @9
    @10
    vk
    vn
    weq
    #
    @4
    @15
    @7
    @96
    @101
    @3
    @14
    @0
    clt
    @101
    @2
    @13
    c1
    cmin
    @1
    @9
    cB
    cexp
    oveq2
    oveq2d
    breq2d
    @101
    @6
    @95
    cE
    clt
    @1
    @9
    @5
    cexp
    oveq2
    breq1d
    anbi12d
    rspccva
    syl2anc
    @94
    @96
    @18
    @15
    @45
    @96
    @18
    wb
    @11
    @45
    @95
    @17
    cE
    clt
    @45
    @95
    c1
    @9
    cexp
    co
    #
    @16
    cdiv
    co
    #
    @17
    @45
    c1
    cc
    wcel
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    @63
    @95
    @103
    wceq
    @45
    1cnd
    wph
    @106
    @44
    wph
    @104
    @105
    @77
    @81
    jca
    adantr
    @44
    @63
    wph
    @66
    adantl
    c1
    cA
    @9
    expdiv
    syl3anc
    @45
    @102
    c1
    @16
    cdiv
    @45
    @99
    @102
    c1
    wceq
    @44
    @99
    wph
    @100
    adantl
    @9
    1exp
    syl
    oveq1d
    eqtrd
    breq1d
    adantr
    anbi2d
    mpbid
    ex
    reximdva
    mpd
end
