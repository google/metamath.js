include "cfv.mm"
include "ccj.mm"
include "ccom.mm"
include "wceq.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "cv.mm"
include "czn.mm"
include "cui.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cof.mm"
include "eqid.mm"
include "cbs.mm"
include "cc.mm"
include "wf.mm"
include "cmulr.mm"
include "cur.mm"
include "c1.mm"
include "cc0.mm"
include "wne.mm"
include "wi.mm"
include "w3a.mm"
include "cjf.mm"
include "dchrf.mm"
include "fco.mm"
include "sylancr.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "dchrelbas3.mm"
include "mpbid.mm"
include "simprd.mm"
include "simp1d.mm"
include "r19.21bi.mm"
include "anasss.mm"
include "fveq2d.mm"
include "adantr.mm"
include "unitss.mm"
include "simprl.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "cjmuld.mm"
include "eqtrd.mm"
include "crg.mm"
include "cn0.mm"
include "ccrg.mm"
include "nnnn0d.mm"
include "zncrng.mm"
include "crngring.mm"
include "3syl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "ringidcl.mm"
include "simp2d.mm"
include "cr.mm"
include "1re.mm"
include "cjre.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "simp3d.mm"
include "sylan.mm"
include "cj0.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqeq12d.mm"
include "wb.mm"
include "ffvelrnda.mm"
include "0cn.mm"
include "cj11.mm"
include "sylancl.mm"
include "bitrd.mm"
include "necon3bid.mm"
include "imbi1d.mm"
include "ralbidva.mm"
include "mpbird.mm"
include "3jca.mm"
include "mpbir2and.mm"
include "dchrmul.mm"
include "fveq1d.mm"
include "cabs.mm"
include "c2.mm"
include "cexp.mm"
include "sseli.mm"
include "sylan2.mm"
include "oveq2d.mm"
include "absvalsqd.mm"
include "simpr.mm"
include "dchrabs.mm"
include "oveq1d.mm"
include "sq1.mm"
include "3eqtr2d.mm"
include "wfn.mm"
include "cvv.mm"
include "ffn.mm"
include "fvexd.mm"
include "adantl.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "dchr1.mm"
include "ralrimiva.mm"
include "dchrmulcl.mm"
include "cgrp.mm"
include "cabl.mm"
include "dchrabl.mm"
include "ablgrp.mm"
include "grpidcl.mm"
include "dchreq.mm"
include "grpinvid1.mm"

theorem dchrinv
  let wph: wff ph
  let cD: class D
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume dchrabs.g: |- G = ( DChr ` N )
  assume dchrabs.d: |- D = ( Base ` G )
  assume dchrabs.x: |- ( ph -> X e. D )
  assume dchrinv.i: |- I = ( invg ` G )


  assert |- ( ph -> ( I ` X ) = ( * o. X ) )

  proof
    wph
    cX
    cI
    cfv
    ccj
    cX
    ccom
    #
    wceq
    #
    cX
    @0
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    wph
    @5
    vx
    cv
    #
    @3
    cfv
    #
    @6
    @4
    cfv
    #
    wceq
    #
    vx
    cN
    czn
    cfv
    #
    cui
    cfv
    #
    wral
    wph
    @9
    vx
    @11
    wph
    @6
    @11
    wcel
    #
    wa
    #
    @7
    @6
    cX
    @0
    cmul
    cof
    co
    #
    cfv
    #
    @8
    @13
    @6
    @3
    @14
    wph
    @3
    @14
    wceq
    @12
    wph
    cD
    @2
    cG
    cN
    cX
    @0
    @10
    dchrabs.g
    @10
    eqid
    #
    dchrabs.d
    @2
    eqid
    #
    dchrabs.x
    wph
    @0
    cD
    wcel
    #
    @10
    cbs
    cfv
    #
    cc
    @0
    wf
    #
    @6
    vy
    cv
    #
    @10
    cmulr
    cfv
    #
    co
    #
    @0
    cfv
    #
    @6
    @0
    cfv
    #
    @21
    @0
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    @11
    wral
    vx
    @11
    wral
    #
    @10
    cur
    cfv
    #
    @0
    cfv
    #
    c1
    wceq
    #
    @25
    cc0
    wne
    #
    @12
    wi
    #
    vx
    @19
    wral
    #
    w3a
    wph
    cc
    cc
    ccj
    wf
    @19
    cc
    cX
    wf
    #
    @20
    cjf
    wph
    @19
    cD
    cG
    cN
    cX
    @10
    dchrabs.g
    @16
    dchrabs.d
    @19
    eqid
    #
    dchrabs.x
    dchrf
    #
    @19
    cc
    cc
    ccj
    cX
    fco
    sylancr
    #
    wph
    @29
    @32
    @35
    wph
    @28
    vx
    vy
    @11
    @11
    wph
    @12
    @21
    @11
    wcel
    #
    wa
    #
    wa
    #
    @23
    cX
    cfv
    #
    ccj
    cfv
    #
    @6
    cX
    cfv
    #
    ccj
    cfv
    #
    @21
    cX
    cfv
    #
    ccj
    cfv
    #
    cmul
    co
    #
    @24
    @27
    @42
    @44
    @45
    @47
    cmul
    co
    #
    ccj
    cfv
    @49
    @42
    @43
    @50
    ccj
    wph
    @12
    @40
    @43
    @50
    wceq
    #
    @13
    @51
    vy
    @11
    wph
    @51
    vy
    @11
    wral
    #
    vx
    @11
    wph
    @52
    vx
    @11
    wral
    #
    @30
    cX
    cfv
    #
    c1
    wceq
    #
    @45
    cc0
    wne
    #
    @12
    wi
    #
    vx
    @19
    wral
    #
    wph
    @36
    @53
    @55
    @58
    w3a
    #
    wph
    cX
    cD
    wcel
    #
    @36
    @59
    wa
    dchrabs.x
    wph
    vx
    vy
    @19
    cD
    @11
    cG
    cN
    cX
    @10
    dchrabs.g
    @16
    @37
    @11
    eqid
    #
    wph
    @60
    cN
    cn
    wcel
    #
    dchrabs.x
    cD
    cG
    cN
    cX
    dchrabs.g
    dchrabs.d
    dchrrcl
    syl
    #
    dchrabs.d
    dchrelbas3
    mpbid
    simprd
    #
    simp1d
    r19.21bi
    r19.21bi
    anasss
    fveq2d
    @42
    @45
    @47
    @42
    @19
    cc
    @6
    cX
    wph
    @36
    @41
    @38
    adantr
    #
    @42
    @11
    @19
    @6
    @19
    @10
    @11
    @37
    @61
    unitss
    #
    wph
    @12
    @40
    simprl
    sseldi
    #
    ffvelrnd
    @42
    @19
    cc
    @21
    cX
    @65
    @42
    @11
    @19
    @21
    @66
    wph
    @12
    @40
    simprr
    sseldi
    #
    ffvelrnd
    cjmuld
    eqtrd
    @42
    @36
    @23
    @19
    wcel
    #
    @24
    @44
    wceq
    @65
    @42
    @10
    crg
    wcel
    #
    @6
    @19
    wcel
    #
    @21
    @19
    wcel
    #
    @69
    wph
    @70
    @41
    wph
    cN
    cn0
    wcel
    @10
    ccrg
    wcel
    @70
    wph
    cN
    @63
    nnnn0d
    cN
    @10
    @16
    zncrng
    @10
    crngring
    3syl
    #
    adantr
    @67
    @68
    @19
    @10
    @22
    @6
    @21
    @37
    @22
    eqid
    ringcl
    syl3anc
    @19
    cc
    @23
    ccj
    cX
    fvco3
    syl2anc
    @42
    @25
    @46
    @26
    @48
    cmul
    @42
    @36
    @71
    @25
    @46
    wceq
    #
    @65
    @67
    @19
    cc
    @6
    ccj
    cX
    fvco3
    #
    syl2anc
    @42
    @36
    @72
    @26
    @48
    wceq
    @65
    @68
    @19
    cc
    @21
    ccj
    cX
    fvco3
    syl2anc
    oveq12d
    3eqtr4d
    ralrimivva
    wph
    @31
    @54
    ccj
    cfv
    #
    c1
    wph
    @36
    @30
    @19
    wcel
    #
    @31
    @76
    wceq
    @38
    wph
    @70
    @77
    @73
    @19
    @10
    @30
    @37
    @30
    eqid
    ringidcl
    syl
    @19
    cc
    @30
    ccj
    cX
    fvco3
    syl2anc
    wph
    @76
    c1
    ccj
    cfv
    #
    c1
    wph
    @54
    c1
    ccj
    wph
    @53
    @55
    @58
    @64
    simp2d
    fveq2d
    c1
    cr
    wcel
    @78
    c1
    wceq
    1re
    c1
    cjre
    ax-mp
    syl6eq
    eqtrd
    wph
    @35
    @58
    wph
    @53
    @55
    @58
    @64
    simp3d
    wph
    @34
    @57
    vx
    @19
    wph
    @71
    wa
    #
    @33
    @56
    @12
    @79
    @25
    cc0
    @45
    cc0
    @79
    @25
    cc0
    wceq
    @46
    cc0
    ccj
    cfv
    #
    wceq
    #
    @45
    cc0
    wceq
    #
    @79
    @25
    @46
    cc0
    @80
    wph
    @36
    @71
    @74
    @38
    @75
    sylan
    #
    cc0
    @80
    wceq
    @79
    @80
    cc0
    cj0
    eqcomi
    a1i
    eqeq12d
    @79
    @45
    cc
    wcel
    #
    cc0
    cc
    wcel
    @81
    @82
    wb
    wph
    @19
    cc
    @6
    cX
    @38
    ffvelrnda
    #
    0cn
    @45
    cc0
    cj11
    sylancl
    bitrd
    necon3bid
    imbi1d
    ralbidva
    mpbird
    3jca
    wph
    vx
    vy
    @19
    cD
    @11
    cG
    cN
    @0
    @10
    dchrabs.g
    @16
    @37
    @61
    @63
    dchrabs.d
    dchrelbas3
    mpbir2and
    #
    dchrmul
    adantr
    fveq1d
    @13
    @45
    @25
    cmul
    co
    #
    c1
    @15
    @8
    @13
    @87
    @45
    @46
    cmul
    co
    @45
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    c1
    @13
    @25
    @46
    @45
    cmul
    @12
    wph
    @71
    @74
    @11
    @19
    @6
    @66
    sseli
    #
    @83
    sylan2
    oveq2d
    @13
    @45
    @12
    wph
    @71
    @84
    @90
    @85
    sylan2
    absvalsqd
    @13
    @89
    c1
    c2
    cexp
    co
    c1
    @13
    @88
    c1
    c2
    cexp
    @13
    @6
    cD
    @11
    cG
    cN
    cX
    @10
    dchrabs.g
    dchrabs.d
    wph
    @60
    @12
    dchrabs.x
    adantr
    @16
    @61
    wph
    @12
    simpr
    #
    dchrabs
    oveq1d
    sq1
    syl6eq
    3eqtr2d
    @13
    cX
    @19
    wfn
    #
    @0
    @19
    wfn
    #
    @19
    cvv
    wcel
    @71
    @15
    @87
    wceq
    @13
    @36
    @92
    wph
    @36
    @12
    @38
    adantr
    @19
    cc
    cX
    ffn
    syl
    wph
    @93
    @12
    wph
    @20
    @93
    @39
    @19
    cc
    @0
    ffn
    syl
    adantr
    @13
    @10
    cbs
    fvexd
    @12
    @71
    wph
    @90
    adantl
    @19
    cmul
    cX
    @0
    cvv
    @6
    fnfvof
    syl22anc
    @13
    @6
    @11
    @4
    cG
    cN
    @10
    dchrabs.g
    @16
    @4
    eqid
    #
    @61
    wph
    @62
    @12
    @63
    adantr
    @91
    dchr1
    3eqtr4d
    eqtrd
    ralrimiva
    wph
    cD
    @11
    vx
    cG
    cN
    @3
    @4
    @10
    dchrabs.g
    @16
    dchrabs.d
    @61
    wph
    cD
    @2
    cG
    cN
    cX
    @0
    @10
    dchrabs.g
    @16
    dchrabs.d
    @17
    dchrabs.x
    @86
    dchrmulcl
    wph
    cG
    cgrp
    wcel
    #
    @4
    cD
    wcel
    wph
    @62
    cG
    cabl
    wcel
    @95
    @63
    cG
    cN
    dchrabs.g
    dchrabl
    cG
    ablgrp
    3syl
    #
    cD
    cG
    @4
    dchrabs.d
    @94
    grpidcl
    syl
    dchreq
    mpbird
    wph
    @95
    @60
    @18
    @1
    @5
    wb
    @96
    dchrabs.x
    @86
    cD
    @2
    cG
    cI
    cX
    @0
    @4
    dchrabs.d
    @17
    @94
    dchrinv.i
    grpinvid1
    syl3anc
    mpbird
end
