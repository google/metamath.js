include "cfv.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "wrex.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rexbidv.mm"
include "wne.mm"
include "wa.mm"
include "cmin.mm"
include "cn.mm"
include "wss.mm"
include "nnssnn0.mm"
include "cr.mm"
include "wcel.mm"
include "crg.mm"
include "adantr.mm"
include "simpr.mm"
include "deg1nn0cl.mm"
include "syl3anc.mm"
include "nn0red.mm"
include "resubcld.mm"
include "arch.mm"
include "syl.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "ad2antrr.mm"
include "nn0re.mm"
include "adantl.mm"
include "ltsubadd2d.mm"
include "biimpd.mm"
include "reximdva.mm"
include "mpd.mm"
include "cc0.mm"
include "0nn0.mm"
include "cmnf.mm"
include "deg1z.mm"
include "0re.mm"
include "readdcl.mm"
include "sylancl.mm"
include "mnflt.mm"
include "eqbrtrd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "pm2.61ne.mm"
include "wi.mm"
include "wral.mm"
include "c1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "imbi2d.mm"
include "weq.mm"
include "ply1ring.mm"
include "ring0cl.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpsubid1.mm"
include "sylan.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "nn0cnd.mm"
include "addid1d.mm"
include "breq12d.mm"
include "biimpa.mm"
include "ex.mm"
include "ralrimiva.mm"
include "cco1.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "cvsca.mm"
include "nn0addcl.mm"
include "simprl.mm"
include "cle.mm"
include "csn.mm"
include "cun.mm"
include "cz.mm"
include "wb.mm"
include "deg1cl.mm"
include "peano2nn0.mm"
include "ad2antlr.mm"
include "nn0addcld.mm"
include "nn0zd.mm"
include "degltlem1.mm"
include "impr.mm"
include "cc.mm"
include "nn0cn.mm"
include "peano2cn.mm"
include "1cnd.mm"
include "addsubassd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "wf.mm"
include "eqid.mm"
include "coe1f.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "ringcl.mm"
include "ply1tmcl.mm"
include "adantrr.mm"
include "leidd.mm"
include "deg1tmle.mm"
include "deg1mulle2.mm"
include "c0g.mm"
include "coe1tmmul2fv.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "ringass.mm"
include "syl13anc.mm"
include "ringlidm.mm"
include "3eqtr3rd.mm"
include "3eqtr4rd.mm"
include "deg1sublt.mm"
include "adantlrr.mm"
include "grpsubcl.mm"
include "simplrr.mm"
include "oveq1.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "cplusg.mm"
include "ad3antrrr.mm"
include "ringacl.mm"
include "grpsubsub4.mm"
include "ringdi.mm"
include "eqtr4d.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "expr.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvralv.mm"
include "sylib.mm"
include "exp32.mm"
include "com12.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem ply1divex
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let c.mi: class .-
  let c.0: class .0.
  let vq: setvar q
  let vd: setvar d
  let vf: setvar f
  let vr: setvar r
  let va: setvar a
  let vg: setvar g
  assume ply1divalg.p: |- P = ( Poly1 ` R )
  assume ply1divalg.d: |- D = ( deg1 ` R )
  assume ply1divalg.b: |- B = ( Base ` P )
  assume ply1divalg.m: |- .- = ( -g ` P )
  assume ply1divalg.z: |- .0. = ( 0g ` P )
  assume ply1divalg.t: |- .xb = ( .r ` P )
  assume ply1divalg.r1: |- ( ph -> R e. Ring )
  assume ply1divalg.f: |- ( ph -> F e. B )
  assume ply1divalg.g1: |- ( ph -> G e. B )
  assume ply1divalg.g2: |- ( ph -> G =/= .0. )
  assume ply1divex.o: |- .1. = ( 1r ` R )
  assume ply1divex.k: |- K = ( Base ` R )
  assume ply1divex.u: |- .x. = ( .r ` R )
  assume ply1divex.i: |- ( ph -> I e. K )
  assume ply1divex.g3: |- ( ph -> ( ( ( coe1 ` G ) ` ( D ` G ) ) .x. I ) = .1. )

  disjoint .0. q
  disjoint F q
  disjoint I q
  disjoint P q
  disjoint R q
  disjoint .- q
  disjoint B q
  disjoint .xb q
  disjoint D q
  disjoint G q
  disjoint ph q
  disjoint .x. q
  disjoint d q
  disjoint .0. d
  disjoint d f
  disjoint F d
  disjoint f q
  disjoint F f
  disjoint f r
  disjoint I f
  disjoint q r
  disjoint I r
  disjoint P f
  disjoint P r
  disjoint R f
  disjoint R r
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a q
  disjoint a r
  disjoint .- a
  disjoint d g
  disjoint d r
  disjoint .- d
  disjoint f g
  disjoint .- f
  disjoint g q
  disjoint g r
  disjoint .- g
  disjoint .- r
  disjoint B a
  disjoint B d
  disjoint B f
  disjoint B g
  disjoint B r
  disjoint .xb a
  disjoint .xb d
  disjoint .xb f
  disjoint .xb g
  disjoint .xb r
  disjoint D a
  disjoint D d
  disjoint D f
  disjoint D g
  disjoint D r
  disjoint G a
  disjoint G d
  disjoint G f
  disjoint G g
  disjoint G r
  disjoint a ph
  disjoint d ph
  disjoint f ph
  disjoint g ph
  disjoint .x. f
  disjoint .x. r
  assert |- ( ph -> E. q e. B ( D ` ( F .- ( G .xb q ) ) ) < ( D ` G ) )

  proof
    wph
    cF
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    vd
    cv
    #
    caddc
    co
    #
    clt
    wbr
    #
    vd
    cn0
    wrex
    #
    cF
    cG
    vq
    cv
    #
    c.xb
    co
    #
    c.mi
    co
    #
    cD
    cfv
    #
    @1
    clt
    wbr
    #
    vq
    cB
    wrex
    #
    wph
    @5
    c.0
    cD
    cfv
    #
    @3
    clt
    wbr
    #
    vd
    cn0
    wrex
    #
    cF
    c.0
    cF
    c.0
    wceq
    #
    @4
    @13
    vd
    cn0
    @15
    @0
    @12
    @3
    clt
    cF
    c.0
    cD
    fveq2
    breq1d
    rexbidv
    wph
    cF
    c.0
    wne
    #
    wa
    #
    @0
    @1
    cmin
    co
    #
    @2
    clt
    wbr
    #
    vd
    cn0
    wrex
    #
    @5
    cn
    cn0
    wss
    @17
    @19
    vd
    cn
    wrex
    #
    @20
    nnssnn0
    @17
    @18
    cr
    wcel
    @21
    @17
    @0
    @1
    @17
    @0
    @17
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    @16
    @0
    cn0
    wcel
    wph
    @22
    @16
    ply1divalg.r1
    adantr
    wph
    @23
    @16
    ply1divalg.f
    adantr
    wph
    @16
    simpr
    cB
    cD
    cP
    cR
    cF
    c.0
    ply1divalg.d
    ply1divalg.p
    ply1divalg.z
    ply1divalg.b
    deg1nn0cl
    syl3anc
    nn0red
    #
    wph
    @1
    cr
    wcel
    #
    @16
    wph
    @1
    wph
    @22
    cG
    cB
    wcel
    #
    cG
    c.0
    wne
    @1
    cn0
    wcel
    #
    ply1divalg.r1
    ply1divalg.g1
    ply1divalg.g2
    cB
    cD
    cP
    cR
    cG
    c.0
    ply1divalg.d
    ply1divalg.p
    ply1divalg.z
    ply1divalg.b
    deg1nn0cl
    syl3anc
    #
    nn0red
    #
    adantr
    resubcld
    @18
    vd
    arch
    syl
    @19
    vd
    cn
    cn0
    ssrexv
    mpsyl
    @17
    @19
    @4
    vd
    cn0
    @17
    @2
    cn0
    wcel
    #
    wa
    #
    @19
    @4
    @31
    @0
    @1
    @2
    @17
    @0
    cr
    wcel
    @30
    @24
    adantr
    wph
    @25
    @16
    @30
    @29
    ad2antrr
    @30
    @2
    cr
    wcel
    @17
    @2
    nn0re
    adantl
    ltsubadd2d
    biimpd
    reximdva
    mpd
    wph
    cc0
    cn0
    wcel
    @12
    @1
    cc0
    caddc
    co
    #
    clt
    wbr
    #
    @14
    0nn0
    wph
    @12
    cmnf
    @32
    clt
    wph
    @22
    @12
    cmnf
    wceq
    ply1divalg.r1
    cD
    cP
    cR
    c.0
    ply1divalg.d
    ply1divalg.p
    ply1divalg.z
    deg1z
    syl
    wph
    @32
    cr
    wcel
    #
    cmnf
    @32
    clt
    wbr
    wph
    @25
    cc0
    cr
    wcel
    @34
    @29
    0re
    @1
    cc0
    readdcl
    sylancl
    @32
    mnflt
    syl
    eqbrtrd
    @13
    @33
    vd
    cc0
    cn0
    @2
    cc0
    wceq
    @3
    @32
    @12
    clt
    @2
    cc0
    @1
    caddc
    oveq2
    breq2d
    rspcev
    sylancr
    pm2.61ne
    wph
    @4
    @11
    vd
    cn0
    wph
    @30
    wa
    #
    @23
    vf
    cv
    #
    cD
    cfv
    #
    @3
    clt
    wbr
    #
    @36
    @7
    c.mi
    co
    #
    cD
    cfv
    #
    @1
    clt
    wbr
    #
    vq
    cB
    wrex
    #
    wi
    #
    vf
    cB
    wral
    #
    @4
    @11
    wi
    #
    wph
    @23
    @30
    ply1divalg.f
    adantr
    @30
    wph
    @44
    wph
    @37
    @1
    va
    cv
    #
    caddc
    co
    #
    clt
    wbr
    #
    @42
    wi
    #
    vf
    cB
    wral
    #
    wi
    wph
    @37
    @32
    clt
    wbr
    #
    @42
    wi
    #
    vf
    cB
    wral
    #
    wi
    wph
    @44
    wi
    #
    wph
    @37
    @1
    @2
    c1
    caddc
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    @42
    wi
    #
    vf
    cB
    wral
    #
    wi
    @54
    va
    vd
    @2
    @46
    cc0
    wceq
    #
    @50
    @53
    wph
    @60
    @49
    @52
    vf
    cB
    @60
    @48
    @51
    @42
    @60
    @47
    @32
    @37
    clt
    @46
    cc0
    @1
    caddc
    oveq2
    breq2d
    imbi1d
    ralbidv
    imbi2d
    va
    vd
    weq
    #
    @50
    @44
    wph
    @61
    @49
    @43
    vf
    cB
    @61
    @48
    @38
    @42
    @61
    @47
    @3
    @37
    clt
    @46
    @2
    @1
    caddc
    oveq2
    breq2d
    imbi1d
    ralbidv
    imbi2d
    #
    @46
    @55
    wceq
    #
    @50
    @59
    wph
    @63
    @49
    @58
    vf
    cB
    @63
    @48
    @57
    @42
    @63
    @47
    @56
    @37
    clt
    @46
    @55
    @1
    caddc
    oveq2
    breq2d
    imbi1d
    ralbidv
    imbi2d
    @62
    wph
    @52
    vf
    cB
    wph
    @36
    cB
    wcel
    #
    wa
    #
    @51
    @42
    @65
    @51
    wa
    c.0
    cB
    wcel
    #
    @36
    cG
    c.0
    c.xb
    co
    #
    c.mi
    co
    #
    cD
    cfv
    #
    @1
    clt
    wbr
    #
    @42
    wph
    @66
    @64
    @51
    wph
    cP
    crg
    wcel
    #
    @66
    wph
    @22
    @71
    ply1divalg.r1
    cP
    cR
    ply1divalg.p
    ply1ring
    syl
    #
    cB
    cP
    c.0
    ply1divalg.b
    ply1divalg.z
    ring0cl
    syl
    ad2antrr
    @65
    @51
    @70
    @65
    @37
    @69
    @32
    @1
    clt
    @65
    @36
    @68
    cD
    @65
    @68
    @36
    c.0
    c.mi
    co
    #
    @36
    wph
    @68
    @73
    wceq
    @64
    wph
    @67
    c.0
    @36
    c.mi
    wph
    @71
    @26
    @67
    c.0
    wceq
    @72
    ply1divalg.g1
    cB
    cP
    c.xb
    cG
    c.0
    ply1divalg.b
    ply1divalg.t
    ply1divalg.z
    ringrz
    syl2anc
    oveq2d
    adantr
    wph
    cP
    cgrp
    wcel
    #
    @64
    @73
    @36
    wceq
    wph
    @71
    @74
    @72
    cP
    ringgrp
    syl
    #
    cB
    cP
    c.mi
    @36
    c.0
    ply1divalg.b
    ply1divalg.z
    ply1divalg.m
    grpsubid1
    sylan
    eqtr2d
    fveq2d
    wph
    @32
    @1
    wceq
    @64
    wph
    @1
    wph
    @1
    @28
    nn0cnd
    addid1d
    adantr
    breq12d
    biimpa
    @41
    @70
    vq
    c.0
    cB
    @6
    c.0
    wceq
    #
    @40
    @69
    @1
    clt
    @76
    @39
    @68
    cD
    @76
    @7
    @67
    @36
    c.mi
    @6
    c.0
    cG
    c.xb
    oveq2
    oveq2d
    fveq2d
    breq1d
    rspcev
    syl2anc
    ex
    ralrimiva
    @30
    wph
    @44
    @59
    wph
    @30
    @44
    @59
    wi
    wph
    @30
    @44
    @59
    wph
    @30
    @44
    wa
    wa
    #
    vg
    cv
    #
    cD
    cfv
    #
    @56
    clt
    wbr
    #
    @78
    cG
    vr
    cv
    #
    c.xb
    co
    #
    c.mi
    co
    #
    cD
    cfv
    #
    @1
    clt
    wbr
    #
    vr
    cB
    wrex
    #
    wi
    #
    vg
    cB
    wral
    @59
    @77
    @87
    vg
    cB
    @77
    @78
    cB
    wcel
    #
    @80
    @86
    @77
    @88
    @80
    wa
    #
    wa
    #
    @78
    cG
    cI
    @3
    @78
    cco1
    cfv
    #
    cfv
    #
    c.x
    co
    #
    @2
    cR
    cv1
    cfv
    #
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    cP
    cvsca
    cfv
    #
    co
    #
    c.xb
    co
    #
    c.mi
    co
    #
    @7
    c.mi
    co
    #
    cD
    cfv
    #
    @1
    clt
    wbr
    #
    vq
    cB
    wrex
    #
    @86
    @90
    @100
    cD
    cfv
    #
    @3
    clt
    wbr
    #
    @104
    wph
    @30
    @89
    @106
    @44
    @35
    @89
    wa
    #
    @91
    cB
    @99
    cco1
    cfv
    #
    cD
    cP
    cR
    @78
    @99
    @3
    c.mi
    ply1divalg.d
    ply1divalg.p
    ply1divalg.b
    ply1divalg.m
    @35
    @3
    cn0
    wcel
    #
    @89
    wph
    @27
    @30
    @109
    @28
    @1
    @2
    nn0addcl
    sylan
    adantr
    wph
    @22
    @30
    @89
    ply1divalg.r1
    ad2antrr
    @35
    @88
    @80
    simprl
    @107
    @79
    @56
    c1
    cmin
    co
    #
    @3
    cle
    @35
    @88
    @80
    @79
    @110
    cle
    wbr
    #
    @35
    @88
    wa
    #
    @80
    @111
    @112
    @79
    cn0
    cmnf
    csn
    cun
    wcel
    #
    @56
    cz
    wcel
    @80
    @111
    wb
    @88
    @113
    @35
    cB
    cD
    cP
    cR
    @78
    ply1divalg.d
    ply1divalg.p
    ply1divalg.b
    deg1cl
    adantl
    @112
    @56
    @112
    @1
    @55
    wph
    @27
    @30
    @88
    @28
    ad2antrr
    #
    @30
    @55
    cn0
    wcel
    wph
    @88
    @2
    peano2nn0
    ad2antlr
    nn0addcld
    nn0zd
    @79
    @56
    degltlem1
    syl2anc
    biimpd
    impr
    @35
    @110
    @3
    wceq
    @89
    @35
    @110
    @1
    @55
    c1
    cmin
    co
    #
    caddc
    co
    @3
    @35
    @1
    @55
    c1
    @35
    @1
    wph
    @27
    @30
    @28
    adantr
    nn0cnd
    @35
    @2
    cc
    wcel
    #
    @55
    cc
    wcel
    @30
    @116
    wph
    @2
    nn0cn
    #
    adantl
    #
    @2
    peano2cn
    syl
    @35
    1cnd
    addsubassd
    @35
    @115
    @2
    @1
    caddc
    @35
    @116
    c1
    cc
    wcel
    @115
    @2
    wceq
    @118
    ax-1cn
    @2
    c1
    pncan
    sylancl
    oveq2d
    eqtrd
    adantr
    breqtrd
    @35
    @88
    @99
    cB
    wcel
    #
    @80
    @112
    @71
    @26
    @98
    cB
    wcel
    #
    @119
    wph
    @71
    @30
    @88
    @72
    ad2antrr
    wph
    @26
    @30
    @88
    ply1divalg.g1
    ad2antrr
    #
    @112
    @22
    @93
    cK
    wcel
    #
    @30
    @120
    wph
    @22
    @30
    @88
    ply1divalg.r1
    ad2antrr
    #
    @112
    @22
    cI
    cK
    wcel
    #
    @92
    cK
    wcel
    #
    @122
    @123
    wph
    @124
    @30
    @88
    ply1divex.i
    ad2antrr
    #
    @112
    cn0
    cK
    @3
    @91
    @88
    cn0
    cK
    @91
    wf
    @35
    @91
    cB
    cP
    cR
    @78
    cK
    @91
    eqid
    #
    ply1divalg.b
    ply1divalg.p
    ply1divex.k
    coe1f
    adantl
    @112
    @1
    @2
    @114
    wph
    @30
    @88
    simplr
    #
    nn0addcld
    ffvelrnd
    #
    cK
    cR
    c.x
    cI
    @92
    ply1divex.k
    ply1divex.u
    ringcl
    syl3anc
    #
    @128
    cB
    @93
    @2
    cP
    cR
    @97
    @96
    cK
    @95
    @94
    ply1divex.k
    ply1divalg.p
    @94
    eqid
    #
    @97
    eqid
    #
    @95
    eqid
    #
    @96
    eqid
    #
    ply1divalg.b
    ply1tmcl
    syl3anc
    #
    cB
    cP
    c.xb
    cG
    @98
    ply1divalg.b
    ply1divalg.t
    ringcl
    syl3anc
    #
    adantrr
    @35
    @88
    @99
    cD
    cfv
    @3
    cle
    wbr
    @80
    @112
    cB
    cD
    cR
    c.xb
    cG
    @98
    @1
    @2
    cP
    ply1divalg.p
    ply1divalg.d
    @123
    ply1divalg.b
    ply1divalg.t
    @121
    @135
    @114
    @128
    @112
    @1
    @112
    @1
    @114
    nn0red
    leidd
    @112
    @22
    @122
    @30
    @98
    cD
    cfv
    @2
    cle
    wbr
    @123
    @130
    @128
    @93
    cD
    cP
    cR
    @97
    @96
    @2
    cK
    @95
    @94
    ply1divalg.d
    ply1divex.k
    ply1divalg.p
    @131
    @132
    @133
    @134
    deg1tmle
    syl3anc
    deg1mulle2
    adantrr
    @127
    @108
    eqid
    @35
    @88
    @92
    @3
    @108
    cfv
    #
    wceq
    @80
    @112
    @2
    @1
    caddc
    co
    #
    @108
    cfv
    @1
    cG
    cco1
    cfv
    #
    cfv
    #
    @93
    c.x
    co
    #
    @137
    @92
    @112
    cG
    cB
    @93
    @2
    cP
    cR
    c.xb
    @97
    c.x
    @96
    cK
    @95
    @94
    @1
    cR
    c0g
    cfv
    #
    @142
    eqid
    ply1divex.k
    ply1divalg.p
    @131
    @132
    @133
    @134
    ply1divalg.b
    ply1divalg.t
    ply1divex.u
    @121
    @123
    @130
    @128
    @114
    coe1tmmul2fv
    @112
    @3
    @138
    @108
    @112
    @1
    @2
    @112
    @1
    @114
    nn0cnd
    @30
    @116
    wph
    @88
    @117
    ad2antlr
    addcomd
    fveq2d
    @112
    @140
    cI
    c.x
    co
    #
    @92
    c.x
    co
    #
    c.1
    @92
    c.x
    co
    #
    @141
    @92
    wph
    @144
    @145
    wceq
    @30
    @88
    wph
    @143
    c.1
    @92
    c.x
    ply1divex.g3
    oveq1d
    ad2antrr
    @112
    @22
    @140
    cK
    wcel
    @124
    @125
    @144
    @141
    wceq
    @123
    @112
    cn0
    cK
    @1
    @139
    wph
    cn0
    cK
    @139
    wf
    #
    @30
    @88
    wph
    @26
    @146
    ply1divalg.g1
    @139
    cB
    cP
    cR
    cG
    cK
    @139
    eqid
    ply1divalg.b
    ply1divalg.p
    ply1divex.k
    coe1f
    syl
    ad2antrr
    @114
    ffvelrnd
    @126
    @129
    cK
    cR
    c.x
    @140
    cI
    @92
    ply1divex.k
    ply1divex.u
    ringass
    syl13anc
    @112
    @22
    @125
    @145
    @92
    wceq
    @123
    @129
    cK
    cR
    c.x
    c.1
    @92
    ply1divex.k
    ply1divex.u
    ply1divex.o
    ringlidm
    syl2anc
    3eqtr3rd
    3eqtr4rd
    adantrr
    deg1sublt
    adantlrr
    @90
    @100
    cB
    wcel
    #
    @44
    @106
    @104
    wi
    #
    wph
    @30
    @89
    @147
    @44
    @35
    @88
    @147
    @80
    @112
    @74
    @88
    @119
    @147
    wph
    @74
    @30
    @88
    @75
    ad2antrr
    @35
    @88
    simpr
    @136
    cB
    cP
    c.mi
    @78
    @99
    ply1divalg.b
    ply1divalg.m
    grpsubcl
    syl3anc
    adantrr
    adantlrr
    wph
    @30
    @44
    @89
    simplrr
    @43
    @148
    vf
    @100
    cB
    @36
    @100
    wceq
    #
    @38
    @106
    @42
    @104
    @149
    @37
    @105
    @3
    clt
    @36
    @100
    cD
    fveq2
    breq1d
    @149
    @41
    @103
    vq
    cB
    @149
    @40
    @102
    @1
    clt
    @149
    @39
    @101
    cD
    @36
    @100
    @7
    c.mi
    oveq1
    fveq2d
    breq1d
    rexbidv
    imbi12d
    rspcva
    syl2anc
    mpd
    wph
    @30
    @89
    @104
    @86
    wi
    #
    @44
    @35
    @88
    @150
    @80
    @112
    @103
    @86
    vq
    cB
    @112
    @6
    cB
    wcel
    #
    wa
    #
    @6
    @98
    cP
    cplusg
    cfv
    #
    co
    #
    cB
    wcel
    #
    @103
    @78
    cG
    @154
    c.xb
    co
    #
    c.mi
    co
    #
    cD
    cfv
    #
    @1
    clt
    wbr
    #
    @86
    @152
    @71
    @151
    @120
    @155
    wph
    @71
    @30
    @88
    @151
    @72
    ad3antrrr
    #
    @112
    @151
    simpr
    #
    @112
    @120
    @151
    @135
    adantr
    #
    cB
    @153
    cP
    @6
    @98
    ply1divalg.b
    @153
    eqid
    #
    ringacl
    syl3anc
    @152
    @103
    @159
    @152
    @102
    @158
    @1
    clt
    @152
    @101
    @157
    cD
    @152
    @101
    @78
    @7
    @99
    @153
    co
    #
    c.mi
    co
    #
    @157
    @152
    @74
    @88
    @119
    @7
    cB
    wcel
    #
    @101
    @165
    wceq
    wph
    @74
    @30
    @88
    @151
    @75
    ad3antrrr
    @35
    @88
    @151
    simplr
    @112
    @119
    @151
    @136
    adantr
    @152
    @71
    @26
    @151
    @166
    @160
    wph
    @26
    @30
    @88
    @151
    ply1divalg.g1
    ad3antrrr
    #
    @161
    cB
    cP
    c.xb
    cG
    @6
    ply1divalg.b
    ply1divalg.t
    ringcl
    syl3anc
    cB
    @153
    cP
    c.mi
    @78
    @99
    @7
    ply1divalg.b
    @163
    ply1divalg.m
    grpsubsub4
    syl13anc
    @152
    @156
    @164
    @78
    c.mi
    @152
    @71
    @26
    @151
    @120
    @156
    @164
    wceq
    @160
    @167
    @161
    @162
    cB
    @153
    cP
    c.xb
    cG
    @6
    @98
    ply1divalg.b
    @163
    ply1divalg.t
    ringdi
    syl13anc
    oveq2d
    eqtr4d
    fveq2d
    breq1d
    biimpd
    @85
    @159
    vr
    @154
    cB
    @81
    @154
    wceq
    #
    @84
    @158
    @1
    clt
    @168
    @83
    @157
    cD
    @168
    @82
    @156
    @78
    c.mi
    @81
    @154
    cG
    c.xb
    oveq2
    oveq2d
    fveq2d
    breq1d
    rspcev
    syl6an
    rexlimdva
    adantrr
    adantlrr
    mpd
    expr
    ralrimiva
    @87
    @58
    vg
    vf
    cB
    vg
    vf
    weq
    #
    @80
    @57
    @86
    @42
    @169
    @79
    @37
    @56
    clt
    @78
    @36
    cD
    fveq2
    breq1d
    @169
    @86
    @36
    @82
    c.mi
    co
    #
    cD
    cfv
    #
    @1
    clt
    wbr
    #
    vr
    cB
    wrex
    @42
    @169
    @85
    @172
    vr
    cB
    @169
    @84
    @171
    @1
    clt
    @169
    @83
    @170
    cD
    @78
    @36
    @82
    c.mi
    oveq1
    fveq2d
    breq1d
    rexbidv
    @172
    @41
    vr
    vq
    cB
    vr
    vq
    weq
    #
    @171
    @40
    @1
    clt
    @173
    @170
    @39
    cD
    @173
    @82
    @7
    @36
    c.mi
    @81
    @6
    cG
    c.xb
    oveq2
    oveq2d
    fveq2d
    breq1d
    cbvrexv
    syl6bb
    imbi12d
    cbvralv
    sylib
    exp32
    com12
    a2d
    nn0ind
    impcom
    @43
    @45
    vf
    cF
    cB
    @36
    cF
    wceq
    #
    @38
    @4
    @42
    @11
    @174
    @37
    @0
    @3
    clt
    @36
    cF
    cD
    fveq2
    breq1d
    @174
    @41
    @10
    vq
    cB
    @174
    @40
    @9
    @1
    clt
    @174
    @39
    @8
    cD
    @36
    cF
    @7
    c.mi
    oveq1
    fveq2d
    breq1d
    rexbidv
    imbi12d
    rspcva
    syl2anc
    rexlimdva
    mpd
end
