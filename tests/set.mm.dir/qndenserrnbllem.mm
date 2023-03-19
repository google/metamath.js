include "cv.mm"
include "cq.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cbl.mm"
include "cfv.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "wfn.mm"
include "chash.mm"
include "csqrt.mm"
include "cdiv.mm"
include "caddc.mm"
include "cioo.mm"
include "cin.mm"
include "wral.mm"
include "cvv.mm"
include "wss.mm"
include "inss1.mm"
include "qex.mm"
include "ssexg.mm"
include "mp2an.mm"
include "a1i.mm"
include "c0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "cxr.mm"
include "cr.mm"
include "wf.mm"
include "elmapi.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "rexrd.mm"
include "rpred.mm"
include "cn.mm"
include "ne0i.mm"
include "adantl.mm"
include "wb.mm"
include "cfn.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nnred.mm"
include "cc0.mm"
include "0red.mm"
include "nngt0d.mm"
include "ltled.mm"
include "resqrtcld.mm"
include "elrpd.mm"
include "sqrtgt0d.mm"
include "gtned.mm"
include "redivcld.mm"
include "readdcld.mm"
include "crp.mm"
include "rpdivcld.mm"
include "ltaddrpd.mm"
include "qbtwnxr.mm"
include "syl3anc.mm"
include "df-rex.mm"
include "sylib.mm"
include "simprl.mm"
include "qre.mm"
include "ad2antrl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "eliood.mm"
include "elind.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "n0.mm"
include "sylibr.mm"
include "choicefi.mm"
include "sseld.mm"
include "ralimdv.mm"
include "imdistani.mm"
include "ffnfv.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "reex.mm"
include "ssriv.mm"
include "mapss.mm"
include "sseldd.mm"
include "cmul.mm"
include "eqid.mm"
include "cmin.mm"
include "cabs.mm"
include "simpll.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "ineq2d.mm"
include "eleq12d.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "rspa.mm"
include "adantll.mm"
include "elinel2.mm"
include "w3a.mm"
include "ffvelrnda.mm"
include "3adant2.mm"
include "simp2.mm"
include "elioored.mm"
include "cle.mm"
include "sqrtgt0.mm"
include "ioogtlb.mm"
include "abssuble0d.mm"
include "iooltub.mm"
include "ltsub1dd.mm"
include "recnd.mm"
include "cc.mm"
include "3ad2ant1.mm"
include "pncan2d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "adantlrl.mm"
include "rpsqrtcld.mm"
include "rrndistlt.mm"
include "rpcnd.mm"
include "sqrtcld.mm"
include "rpne0d.mm"
include "divcan2d.mm"
include "jca.mm"
include "cxmt.mm"
include "cme.mm"
include "rrxmetfi.mm"
include "metxmet.mm"
include "elbl.mm"

theorem qndenserrnbllem
  let wph: wff ph
  let vy: setvar y
  let cD: class D
  let cE: class E
  let cI: class I
  let cX: class X
  let vi: setvar i
  let vk: setvar k
  let vq: setvar q
  let vx: setvar x
  assume qndenserrnbllem.i: |- ( ph -> I e. Fin )
  assume qndenserrnbllem.n: |- ( ph -> I =/= (/) )
  assume qndenserrnbllem.x: |- ( ph -> X e. ( RR ^m I ) )
  assume qndenserrnbllem.d: |- D = ( dist ` ( RR^ ` I ) )
  assume qndenserrnbllem.e: |- ( ph -> E e. RR+ )

  disjoint E y
  disjoint I y
  disjoint X y
  disjoint ph y
  disjoint E i
  disjoint E k
  disjoint i k
  disjoint i y
  disjoint k y
  disjoint E q
  disjoint k q
  disjoint I i
  disjoint I k
  disjoint I q
  disjoint X i
  disjoint X k
  disjoint X q
  disjoint i ph
  disjoint k ph
  disjoint ph q
  disjoint k x
  assert |- ( ph -> E. y e. ( QQ ^m I ) y e. ( X ( ball ` D ) E ) )

  proof
    wph
    vy
    cv
    #
    cq
    cI
    cmap
    co
    #
    wcel
    #
    @0
    cX
    cE
    cD
    cbl
    cfv
    co
    wcel
    #
    wa
    #
    vy
    wex
    #
    @3
    vy
    @1
    wrex
    wph
    @0
    cI
    wfn
    #
    vk
    cv
    #
    @0
    cfv
    #
    cq
    @7
    cX
    cfv
    #
    @9
    cE
    cI
    chash
    cfv
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    caddc
    co
    #
    cioo
    co
    #
    cin
    #
    wcel
    #
    vk
    cI
    wral
    #
    wa
    #
    vy
    wex
    @5
    wph
    vk
    cI
    @15
    vy
    cvv
    qndenserrnbllem.i
    @15
    cvv
    wcel
    #
    wph
    @7
    cI
    wcel
    #
    wa
    #
    @15
    cq
    wss
    #
    cq
    cvv
    wcel
    #
    @19
    cq
    @14
    inss1
    #
    qex
    @15
    cq
    cvv
    ssexg
    mp2an
    a1i
    @21
    vq
    cv
    #
    @15
    wcel
    #
    vq
    wex
    #
    @15
    c0
    wne
    @21
    @25
    cq
    wcel
    #
    @9
    @25
    clt
    wbr
    #
    @25
    @13
    clt
    wbr
    #
    wa
    #
    wa
    #
    vq
    wex
    #
    @27
    @21
    @31
    vq
    cq
    wrex
    #
    @33
    @21
    @9
    cxr
    wcel
    #
    @13
    cxr
    wcel
    #
    @9
    @13
    clt
    wbr
    @34
    @21
    @9
    @21
    cI
    cr
    @7
    cX
    wph
    cI
    cr
    cX
    wf
    #
    @20
    wph
    cX
    cr
    cI
    cmap
    co
    #
    wcel
    #
    @37
    qndenserrnbllem.x
    cX
    cr
    cI
    elmapi
    syl
    #
    adantr
    wph
    @20
    simpr
    ffvelrnd
    #
    rexrd
    #
    @21
    @13
    @21
    @9
    @12
    @41
    @21
    cE
    @11
    wph
    cE
    cr
    wcel
    #
    @20
    wph
    cE
    qndenserrnbllem.e
    rpred
    #
    adantr
    @21
    @10
    @21
    @10
    @21
    @10
    cn
    wcel
    #
    cI
    c0
    wne
    #
    @20
    @46
    wph
    cI
    @7
    ne0i
    adantl
    wph
    @45
    @46
    wb
    #
    @20
    wph
    cI
    cfn
    wcel
    #
    @47
    qndenserrnbllem.i
    cI
    hashnncl
    syl
    #
    adantr
    mpbird
    #
    nnred
    #
    @21
    cc0
    @10
    @21
    0red
    #
    @51
    @21
    @10
    @50
    nngt0d
    #
    ltled
    resqrtcld
    #
    @21
    cc0
    @11
    @52
    @21
    @10
    @21
    @10
    @51
    @53
    elrpd
    sqrtgt0d
    #
    gtned
    redivcld
    readdcld
    rexrd
    #
    @21
    @9
    @12
    @41
    @21
    cE
    @11
    wph
    cE
    crp
    wcel
    #
    @20
    qndenserrnbllem.e
    adantr
    @21
    @11
    @54
    @55
    elrpd
    rpdivcld
    ltaddrpd
    vq
    @9
    @13
    qbtwnxr
    syl3anc
    @31
    vq
    cq
    df-rex
    sylib
    @21
    @32
    @26
    vq
    @21
    @32
    @26
    @21
    @32
    wa
    #
    cq
    @14
    @25
    @21
    @28
    @31
    simprl
    @58
    @9
    @13
    @25
    @21
    @35
    @32
    @42
    adantr
    @21
    @36
    @32
    @56
    adantr
    @28
    @25
    cr
    wcel
    @21
    @31
    @25
    qre
    #
    ad2antrl
    @21
    @28
    @29
    @30
    simprrl
    @21
    @28
    @29
    @30
    simprrr
    eliood
    elind
    ex
    eximdv
    mpd
    vq
    @15
    n0
    sylibr
    choicefi
    wph
    @18
    @4
    vy
    wph
    @18
    @4
    wph
    @18
    wa
    #
    @2
    @3
    @60
    @2
    cI
    cq
    @0
    wf
    #
    @18
    @61
    wph
    @18
    @6
    @8
    cq
    wcel
    #
    vk
    cI
    wral
    #
    wa
    @61
    @6
    @17
    @63
    @6
    @16
    @62
    vk
    cI
    @6
    @15
    cq
    @8
    @22
    @6
    @24
    a1i
    sseld
    ralimdv
    imdistani
    vk
    cI
    cq
    @0
    ffnfv
    sylibr
    adantl
    wph
    @2
    @61
    wb
    #
    @18
    wph
    @23
    @48
    @64
    @23
    wph
    qex
    a1i
    qndenserrnbllem.i
    cq
    cI
    @0
    cvv
    cfn
    elmapg
    syl2anc
    adantr
    mpbird
    #
    @60
    @3
    @0
    @38
    wcel
    #
    cX
    @0
    cD
    co
    #
    cE
    clt
    wbr
    #
    wa
    #
    @60
    @66
    @68
    @60
    @1
    @38
    @0
    @1
    @38
    wss
    #
    @60
    cr
    cvv
    wcel
    cq
    cr
    wss
    @70
    reex
    vq
    cq
    cr
    @59
    ssriv
    cq
    cr
    cI
    cvv
    mapss
    mp2an
    a1i
    @65
    sseldd
    #
    @60
    @67
    @11
    @12
    cmul
    co
    cE
    clt
    @60
    cD
    vi
    @12
    cI
    @10
    cX
    @0
    wph
    @48
    @18
    qndenserrnbllem.i
    adantr
    wph
    @46
    @18
    qndenserrnbllem.n
    adantr
    @10
    eqid
    wph
    @39
    @18
    qndenserrnbllem.x
    adantr
    @71
    wph
    @17
    vi
    cv
    #
    cI
    wcel
    #
    @72
    cX
    cfv
    #
    @72
    @0
    cfv
    #
    cmin
    co
    cabs
    cfv
    #
    @12
    clt
    wbr
    #
    @6
    wph
    @17
    wa
    #
    @73
    wa
    #
    wph
    @75
    @74
    @74
    @12
    caddc
    co
    #
    cioo
    co
    #
    wcel
    #
    @73
    @77
    wph
    @17
    @73
    simpll
    @79
    @75
    cq
    @81
    cin
    #
    wcel
    #
    @82
    @17
    @73
    @84
    wph
    @17
    @73
    wa
    @84
    vi
    cI
    wral
    #
    @73
    @84
    @17
    @85
    @73
    @17
    @85
    @16
    @84
    vk
    vi
    cI
    @7
    @72
    wceq
    #
    @8
    @75
    @15
    @83
    @7
    @72
    @0
    fveq2
    @86
    @14
    @81
    cq
    @86
    @9
    @74
    @13
    @80
    cioo
    @7
    @72
    cX
    fveq2
    #
    @86
    @9
    @74
    @12
    caddc
    @87
    oveq1d
    oveq12d
    ineq2d
    eleq12d
    cbvralv
    biimpi
    adantr
    @17
    @73
    simpr
    @84
    vi
    cI
    rspa
    syl2anc
    adantll
    @75
    cq
    @81
    elinel2
    syl
    @78
    @73
    simpr
    wph
    @82
    @73
    w3a
    #
    @76
    @75
    @74
    cmin
    co
    #
    @12
    clt
    @88
    @74
    @75
    wph
    @73
    @74
    cr
    wcel
    @82
    wph
    cI
    cr
    @72
    cX
    @40
    ffvelrnda
    #
    3adant2
    #
    @88
    @75
    @74
    @80
    wph
    @82
    @73
    simp2
    #
    elioored
    #
    @88
    @74
    @75
    @91
    @93
    @88
    @74
    cxr
    wcel
    #
    @80
    cxr
    wcel
    #
    @82
    @74
    @75
    clt
    wbr
    @88
    @74
    @91
    rexrd
    #
    wph
    @73
    @95
    @82
    wph
    @73
    wa
    #
    @80
    @97
    @74
    @12
    @90
    @97
    cE
    @11
    wph
    @43
    @73
    @44
    adantr
    @97
    @10
    wph
    @10
    cr
    wcel
    #
    @73
    wph
    @10
    wph
    @45
    @46
    qndenserrnbllem.n
    @49
    mpbird
    #
    nnred
    #
    adantr
    wph
    cc0
    @10
    cle
    wbr
    @73
    wph
    cc0
    @10
    wph
    0red
    #
    @100
    wph
    @10
    @99
    nngt0d
    #
    ltled
    #
    adantr
    resqrtcld
    wph
    @11
    cc0
    wne
    @73
    wph
    cc0
    @11
    @101
    wph
    @98
    cc0
    @10
    clt
    wbr
    cc0
    @11
    clt
    wbr
    @100
    @102
    @10
    sqrtgt0
    syl2anc
    gtned
    #
    adantr
    redivcld
    readdcld
    #
    rexrd
    3adant2
    #
    @92
    @74
    @80
    @75
    ioogtlb
    syl3anc
    ltled
    abssuble0d
    @88
    @89
    @80
    @74
    cmin
    co
    @12
    clt
    @88
    @75
    @80
    @74
    @93
    wph
    @73
    @80
    cr
    wcel
    @82
    @105
    3adant2
    @91
    @88
    @94
    @95
    @82
    @75
    @80
    clt
    wbr
    @96
    @106
    @92
    @74
    @80
    @75
    iooltub
    syl3anc
    ltsub1dd
    @88
    @74
    @12
    @88
    @74
    @91
    recnd
    wph
    @82
    @12
    cc
    wcel
    @73
    wph
    @12
    wph
    cE
    @11
    @44
    wph
    @10
    @100
    @103
    resqrtcld
    @104
    redivcld
    recnd
    3ad2ant1
    pncan2d
    breqtrd
    eqbrtrd
    syl3anc
    adantlrl
    @60
    cE
    @11
    wph
    @57
    @18
    qndenserrnbllem.e
    adantr
    #
    @60
    @10
    wph
    @10
    crp
    wcel
    @18
    wph
    @10
    @100
    @102
    elrpd
    adantr
    #
    rpsqrtcld
    #
    rpdivcld
    qndenserrnbllem.d
    rrndistlt
    @60
    cE
    @11
    @60
    cE
    @107
    rpcnd
    @60
    @10
    @60
    @10
    @108
    rpcnd
    sqrtcld
    @60
    @11
    @109
    rpne0d
    divcan2d
    breqtrd
    jca
    wph
    @3
    @69
    wb
    #
    @18
    wph
    cD
    @38
    cxmt
    cfv
    wcel
    #
    @39
    cE
    cxr
    wcel
    @110
    wph
    cD
    @38
    cme
    cfv
    wcel
    #
    @111
    wph
    @48
    @112
    qndenserrnbllem.i
    cD
    cI
    qndenserrnbllem.d
    rrxmetfi
    syl
    cD
    @38
    metxmet
    syl
    qndenserrnbllem.x
    wph
    cE
    @44
    rexrd
    @0
    cD
    cX
    cE
    @38
    elbl
    syl3anc
    adantr
    mpbird
    jca
    ex
    eximdv
    mpd
    @3
    vy
    @1
    df-rex
    sylibr
end
