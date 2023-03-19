include "co1.mm"
include "wcel.mm"
include "cc0.mm"
include "crli.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cdm.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "cc.mm"
include "wf.mm"
include "wfn.mm"
include "o1f.mm"
include "adantr.mm"
include "ffn.mm"
include "syl.mm"
include "rlimf.mm"
include "adantl.mm"
include "cr.mm"
include "wss.mm"
include "o1dm.mm"
include "reex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "rlimss.mm"
include "eqid.mm"
include "eqidd.mm"
include "offval.mm"
include "cle.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "o1bdd.mm"
include "mpdan.mm"
include "ad2antrr.mm"
include "cmin.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "fvexd.mm"
include "ralrimiva.mm"
include "simplr.mm"
include "recn.mm"
include "ad2antll.mm"
include "abscld.mm"
include "absge0d.mm"
include "ge0p1rpd.mm"
include "rpdivcld.mm"
include "feqmptd.mm"
include "simpr.mm"
include "eqbrtrrd.mm"
include "rlimi.mm"
include "cif.mm"
include "inss1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "inss2.mm"
include "anim12i.mm"
include "r19.26.mm"
include "sylibr.mm"
include "prth.mm"
include "ralimi.mm"
include "wb.mm"
include "simplrl.mm"
include "simprl.mm"
include "syl5ss.mm"
include "ad3antrrr.mm"
include "simprr.mm"
include "sseldd.mm"
include "maxle.mm"
include "syl3anc.mm"
include "biimpd.mm"
include "sseli.mm"
include "ffvelrnd.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rpred.mm"
include "ltle.mm"
include "syl2anc.mm"
include "sylbid.mm"
include "anim2d.mm"
include "jca.mm"
include "simplrr.mm"
include "lemul12a.mm"
include "syl22anc.mm"
include "absmuld.mm"
include "recnd.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divassd.mm"
include "peano2re.mm"
include "leabsd.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "ltmul1dd.mm"
include "remulcld.mm"
include "ltdivmuld.mm"
include "mpbird.mm"
include "mulcld.mm"
include "lelttr.mm"
include "mpan2d.mm"
include "sylbird.mm"
include "3syld.mm"
include "imim12d.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "ifcld.mm"
include "jctild.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl56.mm"
include "expcomd.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "rexlimdvva.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "rlim0.mm"
include "eqbrtrd.mm"

theorem o1rlimmul
  let cF: class F
  let cG: class G
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n


  assert |- ( ( F e. O(1) /\ G ~~>r 0 ) -> ( F oF x. G ) ~~>r 0 )

  proof
    cF
    co1
    wcel
    #
    cG
    cc0
    crli
    wbr
    #
    wa
    #
    cF
    cG
    cmul
    cof
    co
    vx
    cF
    cdm
    #
    cG
    cdm
    #
    cin
    #
    vx
    cv
    #
    cF
    cfv
    #
    @6
    cG
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    crli
    @2
    vx
    @3
    @4
    @7
    @8
    cmul
    @5
    cF
    cG
    cvv
    cvv
    @2
    @3
    cc
    cF
    wf
    #
    cF
    @3
    wfn
    @0
    @11
    @1
    cF
    o1f
    #
    adantr
    #
    @3
    cc
    cF
    ffn
    syl
    @2
    @4
    cc
    cG
    wf
    #
    cG
    @4
    wfn
    @1
    @14
    @0
    cc0
    cG
    rlimf
    adantl
    #
    @4
    cc
    cG
    ffn
    syl
    @2
    @3
    cr
    wss
    #
    cr
    cvv
    wcel
    #
    @3
    cvv
    wcel
    @0
    @16
    @1
    cF
    o1dm
    adantr
    #
    reex
    @3
    cr
    cvv
    ssexg
    sylancl
    @2
    @4
    cr
    wss
    #
    @17
    @4
    cvv
    wcel
    @1
    @19
    @0
    cc0
    cG
    rlimss
    adantl
    reex
    @4
    cr
    cvv
    ssexg
    sylancl
    @5
    eqid
    @2
    @6
    @3
    wcel
    #
    wa
    @7
    eqidd
    @2
    @6
    @4
    wcel
    #
    wa
    @8
    eqidd
    offval
    @2
    @10
    cc0
    crli
    wbr
    vz
    cv
    #
    @6
    cle
    wbr
    #
    @9
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vx
    @5
    wral
    #
    vz
    cr
    wrex
    #
    vy
    crp
    wral
    @2
    @29
    vy
    crp
    @2
    @25
    crp
    wcel
    #
    wa
    #
    va
    cv
    #
    @6
    cle
    wbr
    #
    @7
    cabs
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    wi
    #
    vx
    @3
    wral
    #
    vm
    cr
    wrex
    va
    cr
    wrex
    #
    @29
    @0
    @39
    @1
    @30
    @0
    @11
    @39
    @12
    va
    vx
    @3
    vm
    cF
    o1bdd
    mpdan
    ad2antrr
    @31
    @38
    @29
    va
    vm
    cr
    cr
    @31
    @32
    cr
    wcel
    #
    @35
    cr
    wcel
    #
    wa
    #
    wa
    #
    vb
    cv
    #
    @6
    cle
    wbr
    #
    @8
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @25
    @35
    cabs
    cfv
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    clt
    wbr
    #
    wi
    #
    vx
    @4
    wral
    #
    vb
    cr
    wrex
    @38
    @29
    wi
    #
    @43
    vb
    vx
    @4
    @8
    cc0
    @50
    cvv
    @43
    @8
    cvv
    wcel
    vx
    @4
    @43
    @21
    wa
    @6
    cG
    fvexd
    ralrimiva
    @43
    @25
    @49
    @2
    @30
    @42
    simplr
    #
    @43
    @48
    @43
    @35
    @41
    @35
    cc
    wcel
    @31
    @40
    @35
    recn
    ad2antll
    #
    abscld
    #
    @43
    @35
    @56
    absge0d
    ge0p1rpd
    #
    rpdivcld
    #
    @2
    vx
    @4
    @8
    cmpt
    #
    cc0
    crli
    wbr
    @30
    @42
    @2
    cG
    @60
    cc0
    crli
    @2
    vx
    @4
    cc
    cG
    @15
    feqmptd
    @0
    @1
    simpr
    eqbrtrrd
    ad2antrr
    rlimi
    @43
    @53
    @54
    vb
    cr
    @43
    @44
    cr
    wcel
    #
    wa
    #
    @38
    @53
    @29
    @38
    @53
    wa
    #
    @33
    @45
    wa
    #
    @36
    @51
    wa
    #
    wi
    #
    vx
    @5
    wral
    #
    @62
    @32
    @44
    cle
    wbr
    #
    @44
    @32
    cif
    #
    cr
    wcel
    #
    @69
    @6
    cle
    wbr
    #
    @26
    wi
    #
    vx
    @5
    wral
    #
    wa
    @29
    @63
    @37
    @52
    wa
    #
    vx
    @5
    wral
    #
    @67
    @63
    @37
    vx
    @5
    wral
    #
    @52
    vx
    @5
    wral
    #
    wa
    @75
    @38
    @76
    @53
    @77
    @5
    @3
    wss
    @38
    @76
    wi
    @3
    @4
    inss1
    #
    @37
    vx
    @5
    @3
    ssralv
    ax-mp
    @5
    @4
    wss
    @53
    @77
    wi
    @3
    @4
    inss2
    #
    @52
    vx
    @5
    @4
    ssralv
    ax-mp
    anim12i
    @37
    @52
    vx
    @5
    r19.26
    sylibr
    @74
    @66
    vx
    @5
    @33
    @36
    @45
    @51
    prth
    ralimi
    syl
    @62
    @67
    @73
    @70
    @62
    @66
    @72
    vx
    @5
    @43
    @61
    @6
    @5
    wcel
    #
    @66
    @72
    wi
    @43
    @61
    @80
    wa
    #
    wa
    #
    @71
    @64
    @65
    @26
    @82
    @71
    @64
    @82
    @40
    @61
    @6
    cr
    wcel
    @71
    @64
    wb
    @31
    @40
    @41
    @81
    simplrl
    @43
    @61
    @80
    simprl
    @82
    @5
    cr
    @6
    @2
    @5
    cr
    wss
    @30
    @42
    @81
    @2
    @5
    @3
    cr
    @78
    @18
    syl5ss
    #
    ad3antrrr
    @43
    @61
    @80
    simprr
    sseldd
    @32
    @44
    @6
    maxle
    syl3anc
    biimpd
    @82
    @65
    @36
    @8
    cabs
    cfv
    #
    @50
    cle
    wbr
    #
    wa
    #
    @34
    @84
    cmul
    co
    #
    @35
    @50
    cmul
    co
    #
    cle
    wbr
    #
    @26
    @82
    @51
    @85
    @36
    @82
    @51
    @84
    @50
    clt
    wbr
    #
    @85
    @82
    @47
    @84
    @50
    clt
    @82
    @46
    @8
    cabs
    @82
    @8
    @82
    @4
    cc
    @6
    cG
    @2
    @14
    @30
    @42
    @81
    @15
    ad3antrrr
    @80
    @21
    @43
    @61
    @5
    @4
    @6
    @79
    sseli
    #
    ad2antll
    ffvelrnd
    #
    subid1d
    fveq2d
    breq1d
    @82
    @84
    cr
    wcel
    #
    @50
    cr
    wcel
    #
    @90
    @85
    wi
    @82
    @8
    @92
    abscld
    #
    @82
    @50
    @43
    @50
    crp
    wcel
    @81
    @59
    adantr
    rpred
    #
    @84
    @50
    ltle
    syl2anc
    sylbid
    anim2d
    @82
    @34
    cr
    wcel
    #
    cc0
    @34
    cle
    wbr
    #
    wa
    @41
    @93
    cc0
    @84
    cle
    wbr
    #
    wa
    @94
    @86
    @89
    wi
    @82
    @97
    @98
    @82
    @7
    @82
    @3
    cc
    @6
    cF
    @2
    @11
    @30
    @42
    @81
    @13
    ad3antrrr
    @80
    @20
    @43
    @61
    @5
    @3
    @6
    @78
    sseli
    #
    ad2antll
    ffvelrnd
    #
    abscld
    @82
    @7
    @101
    absge0d
    jca
    @31
    @40
    @41
    @81
    simplrr
    #
    @82
    @93
    @99
    @95
    @82
    @8
    @92
    absge0d
    jca
    @96
    @34
    @35
    @84
    @50
    lemul12a
    syl22anc
    @82
    @89
    @24
    @88
    cle
    wbr
    #
    @26
    @82
    @24
    @87
    @88
    cle
    @82
    @7
    @8
    @101
    @92
    absmuld
    breq1d
    @82
    @103
    @88
    @25
    clt
    wbr
    #
    @26
    @82
    @35
    @25
    cmul
    co
    #
    @49
    cdiv
    co
    #
    @88
    @25
    clt
    @82
    @35
    @25
    @49
    @82
    @35
    @102
    recnd
    @82
    @25
    @43
    @30
    @81
    @55
    adantr
    #
    rpcnd
    @82
    @49
    @43
    @49
    crp
    wcel
    @81
    @58
    adantr
    #
    rpcnd
    @82
    @49
    @108
    rpne0d
    divassd
    @82
    @106
    @25
    clt
    wbr
    @105
    @49
    @25
    cmul
    co
    clt
    wbr
    @82
    @35
    @49
    @25
    @102
    @43
    @49
    cr
    wcel
    #
    @81
    @43
    @48
    cr
    wcel
    #
    @109
    @57
    @48
    peano2re
    syl
    adantr
    #
    @107
    @82
    @35
    @48
    @49
    @102
    @43
    @110
    @81
    @57
    adantr
    #
    @111
    @82
    @35
    @102
    leabsd
    @82
    @48
    @112
    ltp1d
    lelttrd
    ltmul1dd
    @82
    @105
    @25
    @49
    @82
    @35
    @25
    @102
    @82
    @25
    @107
    rpred
    #
    remulcld
    @113
    @108
    ltdivmuld
    mpbird
    eqbrtrrd
    @82
    @24
    cr
    wcel
    @88
    cr
    wcel
    @25
    cr
    wcel
    @103
    @104
    wa
    @26
    wi
    @82
    @9
    @82
    @7
    @8
    @101
    @92
    mulcld
    abscld
    @82
    @35
    @50
    @102
    @96
    remulcld
    @113
    @24
    @88
    @25
    lelttr
    syl3anc
    mpan2d
    sylbird
    3syld
    imim12d
    anassrs
    ralimdva
    @62
    @68
    @44
    @32
    cr
    @43
    @61
    simpr
    @31
    @40
    @41
    @61
    simplrl
    ifcld
    jctild
    @28
    @73
    vz
    @69
    cr
    @22
    @69
    wceq
    #
    @27
    @72
    vx
    @5
    @114
    @23
    @71
    @26
    @22
    @69
    @6
    cle
    breq1
    imbi1d
    ralbidv
    rspcev
    syl56
    expcomd
    rexlimdva
    mpd
    rexlimdvva
    mpd
    ralrimiva
    @2
    vy
    vz
    vx
    @5
    @9
    @2
    @9
    cc
    wcel
    vx
    @5
    @2
    @80
    wa
    @7
    @8
    @2
    @11
    @20
    @7
    cc
    wcel
    @80
    @13
    @100
    @3
    cc
    @6
    cF
    ffvelrn
    syl2an
    @2
    @14
    @21
    @8
    cc
    wcel
    @80
    @15
    @91
    @4
    cc
    @6
    cG
    ffvelrn
    syl2an
    mulcld
    ralrimiva
    @83
    rlim0
    mpbird
    eqbrtrd
end
