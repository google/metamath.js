include "co.mm"
include "cmul.mm"
include "cof.mm"
include "dchrmul.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cc.mm"
include "wf.mm"
include "cv.mm"
include "cmulr.mm"
include "wceq.mm"
include "cui.mm"
include "wral.mm"
include "cur.mm"
include "c1.mm"
include "cc0.mm"
include "wne.mm"
include "wi.mm"
include "w3a.mm"
include "cvv.mm"
include "wa.mm"
include "mulcl.mm"
include "adantl.mm"
include "eqid.mm"
include "dchrf.mm"
include "fvexd.mm"
include "inidm.mm"
include "off.mm"
include "unitcl.mm"
include "anim12i.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "dchrelbas2.mm"
include "mpbid.mm"
include "simpld.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cnfldmul.mm"
include "mhmlin.mm"
include "3expb.mm"
include "sylan.mm"
include "oveq12d.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "simpr.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "mul4d.mm"
include "eqtrd.mm"
include "wfn.mm"
include "ffn.mm"
include "adantr.mm"
include "crg.mm"
include "cn0.mm"
include "ccrg.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "3syl.mm"
include "ringcl.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "simprr.mm"
include "3eqtr4d.mm"
include "sylan2.mm"
include "ralrimivva.mm"
include "ringidcl.mm"
include "ringidval.mm"
include "cnfld1.mm"
include "mhm0.mm"
include "1t1e1.mm"
include "syl6eq.mm"
include "neeq1d.mm"
include "mulne0bd.mm"
include "bitr4d.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "adantrd.mm"
include "sylbid.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "dchrelbas3.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"

theorem dchrmulcl
  let wph: wff ph
  let cD: class D
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let c.1: class .1.
  let vk: setvar k
  let cB: class B
  let cK: class K
  let cL: class L
  let cU: class U
  let cA: class A
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrmul.t: |- .x. = ( +g ` G )
  assume dchrmul.x: |- ( ph -> X e. D )
  assume dchrmul.y: |- ( ph -> Y e. D )


  assert |- ( ph -> ( X .x. Y ) e. D )

  proof
    wph
    cX
    cY
    c.x
    co
    cX
    cY
    cmul
    cof
    co
    #
    cD
    wph
    cD
    c.x
    cG
    cN
    cX
    cY
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrmul.t
    dchrmul.x
    dchrmul.y
    dchrmul
    wph
    @0
    cD
    wcel
    cZ
    cbs
    cfv
    #
    cc
    @0
    wf
    vx
    cv
    #
    vy
    cv
    #
    cZ
    cmulr
    cfv
    #
    co
    #
    @0
    cfv
    #
    @2
    @0
    cfv
    #
    @3
    @0
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cZ
    cui
    cfv
    #
    wral
    vx
    @11
    wral
    #
    cZ
    cur
    cfv
    #
    @0
    cfv
    #
    c1
    wceq
    #
    @7
    cc0
    wne
    #
    @2
    @11
    wcel
    #
    wi
    #
    vx
    @1
    wral
    #
    w3a
    wph
    vx
    vy
    @1
    @1
    @1
    cmul
    cc
    cc
    cc
    cX
    cY
    cvv
    cvv
    @2
    cc
    wcel
    @3
    cc
    wcel
    wa
    @2
    @3
    cmul
    co
    cc
    wcel
    wph
    @2
    @3
    mulcl
    adantl
    wph
    @1
    cD
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    @1
    eqid
    #
    dchrmul.x
    dchrf
    #
    wph
    @1
    cD
    cG
    cN
    cY
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    @20
    dchrmul.y
    dchrf
    #
    wph
    cZ
    cbs
    fvexd
    #
    @23
    @1
    inidm
    off
    wph
    @12
    @15
    @19
    wph
    @10
    vx
    vy
    @11
    @11
    @17
    @3
    @11
    wcel
    #
    wa
    wph
    @2
    @1
    wcel
    #
    @3
    @1
    wcel
    #
    wa
    #
    @10
    @17
    @25
    @24
    @26
    @1
    cZ
    @11
    @2
    @20
    @11
    eqid
    #
    unitcl
    @1
    cZ
    @11
    @3
    @20
    @28
    unitcl
    anim12i
    wph
    @27
    wa
    #
    @5
    cX
    cfv
    #
    @5
    cY
    cfv
    #
    cmul
    co
    #
    @2
    cX
    cfv
    #
    @2
    cY
    cfv
    #
    cmul
    co
    #
    @3
    cX
    cfv
    #
    @3
    cY
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @6
    @9
    @29
    @32
    @33
    @36
    cmul
    co
    #
    @34
    @37
    cmul
    co
    #
    cmul
    co
    @39
    @29
    @30
    @40
    @31
    @41
    cmul
    wph
    cX
    cZ
    cmgp
    cfv
    #
    ccnfld
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    #
    @27
    @30
    @40
    wceq
    #
    wph
    @45
    @33
    cc0
    wne
    #
    @17
    wi
    #
    vx
    @1
    wral
    #
    wph
    cX
    cD
    wcel
    #
    @45
    @49
    wa
    dchrmul.x
    wph
    vx
    @1
    cD
    @11
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    @20
    @28
    wph
    @50
    cN
    cn
    wcel
    dchrmul.x
    cD
    cG
    cN
    cX
    dchrmhm.g
    dchrmhm.b
    dchrrcl
    syl
    #
    dchrmhm.b
    dchrelbas2
    mpbid
    #
    simpld
    #
    @45
    @25
    @26
    @46
    @1
    @4
    cmul
    @42
    @43
    cX
    @2
    @3
    @1
    cZ
    @42
    @42
    eqid
    #
    @20
    mgpbas
    #
    cZ
    @4
    @42
    @54
    @4
    eqid
    #
    mgpplusg
    #
    ccnfld
    cmul
    @43
    @43
    eqid
    #
    cnfldmul
    mgpplusg
    #
    mhmlin
    3expb
    sylan
    wph
    cY
    @44
    wcel
    #
    @27
    @31
    @41
    wceq
    #
    wph
    @60
    @34
    cc0
    wne
    #
    @17
    wi
    vx
    @1
    wral
    #
    wph
    cY
    cD
    wcel
    @60
    @63
    wa
    dchrmul.y
    wph
    vx
    @1
    cD
    @11
    cG
    cN
    cY
    cZ
    dchrmhm.g
    dchrmhm.z
    @20
    @28
    @51
    dchrmhm.b
    dchrelbas2
    mpbid
    simpld
    #
    @60
    @25
    @26
    @61
    @1
    @4
    cmul
    @42
    @43
    cY
    @2
    @3
    @55
    @57
    @59
    mhmlin
    3expb
    sylan
    oveq12d
    @29
    @33
    @36
    @34
    @37
    wph
    @25
    @33
    cc
    wcel
    @26
    wph
    @1
    cc
    @2
    cX
    @21
    ffvelrnda
    #
    adantrr
    wph
    @1
    cc
    cX
    wf
    #
    @26
    @36
    cc
    wcel
    @27
    @21
    @25
    @26
    simpr
    #
    @1
    cc
    @3
    cX
    ffvelrn
    syl2an
    wph
    @25
    @34
    cc
    wcel
    @26
    wph
    @1
    cc
    @2
    cY
    @22
    ffvelrnda
    #
    adantrr
    wph
    @1
    cc
    cY
    wf
    #
    @26
    @37
    cc
    wcel
    @27
    @22
    @67
    @1
    cc
    @3
    cY
    ffvelrn
    syl2an
    mul4d
    eqtrd
    @29
    cX
    @1
    wfn
    #
    cY
    @1
    wfn
    #
    @1
    cvv
    wcel
    #
    @5
    @1
    wcel
    #
    @6
    @32
    wceq
    wph
    @70
    @27
    wph
    @66
    @70
    @21
    @1
    cc
    cX
    ffn
    syl
    #
    adantr
    #
    wph
    @71
    @27
    wph
    @69
    @71
    @22
    @1
    cc
    cY
    ffn
    syl
    #
    adantr
    #
    @29
    cZ
    cbs
    fvexd
    #
    wph
    cZ
    crg
    wcel
    #
    @27
    @73
    wph
    cN
    cn0
    wcel
    cZ
    ccrg
    wcel
    @79
    wph
    cN
    @51
    nnnn0d
    cN
    cZ
    dchrmhm.z
    zncrng
    cZ
    crngring
    3syl
    #
    @79
    @25
    @26
    @73
    @1
    cZ
    @4
    @2
    @3
    @20
    @56
    ringcl
    3expb
    sylan
    @1
    cmul
    cX
    cY
    cvv
    @5
    fnfvof
    syl22anc
    @29
    @7
    @35
    @8
    @38
    cmul
    wph
    @25
    @7
    @35
    wceq
    #
    @26
    wph
    @25
    wa
    #
    @70
    @71
    @72
    @25
    @81
    wph
    @70
    @25
    @74
    adantr
    wph
    @71
    @25
    @76
    adantr
    @82
    cZ
    cbs
    fvexd
    wph
    @25
    simpr
    @1
    cmul
    cX
    cY
    cvv
    @2
    fnfvof
    syl22anc
    #
    adantrr
    @29
    @70
    @71
    @72
    @26
    @8
    @38
    wceq
    @75
    @77
    @78
    wph
    @25
    @26
    simprr
    @1
    cmul
    cX
    cY
    cvv
    @3
    fnfvof
    syl22anc
    oveq12d
    3eqtr4d
    sylan2
    ralrimivva
    wph
    @14
    @13
    cX
    cfv
    #
    @13
    cY
    cfv
    #
    cmul
    co
    #
    c1
    wph
    @70
    @71
    @72
    @13
    @1
    wcel
    #
    @14
    @86
    wceq
    @74
    @76
    @23
    wph
    @79
    @87
    @80
    @1
    cZ
    @13
    @20
    @13
    eqid
    #
    ringidcl
    syl
    @1
    cmul
    cX
    cY
    cvv
    @13
    fnfvof
    syl22anc
    wph
    @86
    c1
    c1
    cmul
    co
    c1
    wph
    @84
    c1
    @85
    c1
    cmul
    wph
    @45
    @84
    c1
    wceq
    @53
    @42
    @43
    cX
    c1
    @13
    cZ
    @13
    @42
    @54
    @88
    ringidval
    #
    ccnfld
    c1
    @43
    @58
    cnfld1
    ringidval
    #
    mhm0
    syl
    wph
    @60
    @85
    c1
    wceq
    @64
    @42
    @43
    cY
    c1
    @13
    @89
    @90
    mhm0
    syl
    oveq12d
    1t1e1
    syl6eq
    eqtrd
    wph
    @18
    vx
    @1
    @82
    @16
    @47
    @62
    wa
    #
    @17
    @82
    @16
    @35
    cc0
    wne
    @91
    @82
    @7
    @35
    cc0
    @83
    neeq1d
    @82
    @33
    @34
    @65
    @68
    mulne0bd
    bitr4d
    @82
    @47
    @17
    @62
    wph
    @48
    vx
    @1
    wph
    @45
    @49
    @52
    simprd
    r19.21bi
    adantrd
    sylbid
    ralrimiva
    3jca
    wph
    vx
    vy
    @1
    cD
    @11
    cG
    cN
    @0
    cZ
    dchrmhm.g
    dchrmhm.z
    @20
    @28
    @51
    dchrmhm.b
    dchrelbas3
    mpbir2and
    eqeltrd
end
