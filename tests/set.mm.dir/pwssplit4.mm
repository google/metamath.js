include "clmod.mm"
include "wcel.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "clmhm.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "clmim.mm"
include "cv.mm"
include "cres.mm"
include "cmpt.mm"
include "wss.mm"
include "csn.mm"
include "cxp.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "clss.mm"
include "ssun2.mm"
include "a1i.mm"
include "eqid.mm"
include "pwssplit3.mm"
include "syld3an3.mm"
include "c0g.mm"
include "cmnd.mm"
include "cvv.mm"
include "cgrp.mm"
include "simp1.mm"
include "lmodgrp.mm"
include "grpmnd.mm"
include "3syl.mm"
include "ssun1.mm"
include "ssexg.mm"
include "mpan.mm"
include "3ad2ant2.mm"
include "pws0g.mm"
include "syl2anc.mm"
include "eqeq2d.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "ccnv.mm"
include "cima.mm"
include "fvex.mm"
include "mptiniseg.mm"
include "eqcomi.mm"
include "lmhmkerlss.mm"
include "syl.mm"
include "eqeltrd.mm"
include "reslmhm.mm"
include "syl5eqel.mm"
include "wf1.mm"
include "crn.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "fvtresfn.mm"
include "eqcomd.mm"
include "eqeqan12rd.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "uneq12.mm"
include "resundi.mm"
include "xpundir.mm"
include "3eqtr4g.mm"
include "adantll.mm"
include "adantl.mm"
include "wf.mm"
include "wfn.mm"
include "simpl1.mm"
include "simp2.mm"
include "adantr.mm"
include "simprll.mm"
include "pwselbas.mm"
include "ffn.mm"
include "fnresdm.mm"
include "csubg.mm"
include "pwslmod.mm"
include "3adant3.mm"
include "lsssubg.mm"
include "subg0.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "exp32.mm"
include "syl5bi.mm"
include "imp.mm"
include "sylbid.mm"
include "ralrimiva.mm"
include "cghm.mm"
include "wb.mm"
include "lmghm.mm"
include "ressbas2.mm"
include "ghmf1.mm"
include "mpbird.mm"
include "lmhmf.mm"
include "frn.mm"
include "pwselbasb.mm"
include "biimpa.mm"
include "eqeltri.mm"
include "fconst.mm"
include "mndidcl.mm"
include "snssd.mm"
include "fssd.mm"
include "incom.mm"
include "simp3.mm"
include "fun.mm"
include "syl21anc.mm"
include "uncom.mm"
include "unidm.mm"
include "feq23i.mm"
include "sylib.mm"
include "simpl3.mm"
include "fnresdisj.mm"
include "mpbid.mm"
include "fnconstg.mm"
include "mp2b.mm"
include "uneq12d.mm"
include "resundir.mm"
include "un0.mm"
include "eqtr2i.mm"
include "sylanbrc.mm"
include "resexg.mm"
include "fvmptg.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "syl6eq.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "dff1o5.mm"
include "islmim.mm"

theorem pwssplit4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cV: class V
  let c.0: class .0.
  let va: setvar a
  assume pwssplit4.e: |- E = ( R ^s ( A u. B ) )
  assume pwssplit4.g: |- G = ( Base ` E )
  assume pwssplit4.z: |- .0. = ( 0g ` R )
  assume pwssplit4.k: |- K = { y e. G | ( y |` A ) = ( A X. { .0. } ) }
  assume pwssplit4.f: |- F = ( x e. K |-> ( x |` B ) )
  assume pwssplit4.c: |- C = ( R ^s A )
  assume pwssplit4.d: |- D = ( R ^s B )
  assume pwssplit4.l: |- L = ( E |`s K )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint E x
  disjoint E y
  disjoint G x
  disjoint G y
  disjoint K x
  disjoint L x
  disjoint R x
  disjoint R y
  disjoint V x
  disjoint V y
  disjoint .0. x
  disjoint .0. y
  disjoint A a
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint D a
  disjoint F a
  disjoint K a
  disjoint L a
  disjoint R a
  disjoint V a
  assert |- ( ( R e. LMod /\ ( A u. B ) e. V /\ ( A i^i B ) = (/) ) -> F e. ( L LMIso D ) )

  proof
    cR
    clmod
    wcel
    #
    cA
    cB
    cun
    #
    cV
    wcel
    #
    cA
    cB
    cin
    #
    c0
    wceq
    #
    w3a
    #
    cF
    cL
    cD
    clmhm
    co
    #
    wcel
    #
    cK
    cD
    cbs
    cfv
    #
    cF
    wf1o
    #
    cF
    cL
    cD
    clmim
    co
    wcel
    @5
    cF
    vx
    cG
    vx
    cv
    #
    cB
    cres
    #
    cmpt
    #
    cK
    cres
    #
    @6
    cF
    vx
    cK
    @11
    cmpt
    #
    @13
    pwssplit4.f
    cK
    cG
    wss
    #
    @13
    @14
    wceq
    cK
    vy
    cv
    #
    cA
    cres
    #
    cA
    c.0
    csn
    #
    cxp
    #
    wceq
    #
    vy
    cG
    crab
    #
    cG
    pwssplit4.k
    @20
    vy
    cG
    ssrab2
    eqsstri
    #
    vx
    cG
    cK
    @11
    resmpt
    ax-mp
    eqtr4i
    @5
    @12
    cE
    cD
    clmhm
    co
    wcel
    #
    cK
    cE
    clss
    cfv
    #
    wcel
    #
    @13
    @6
    wcel
    @0
    @2
    @4
    cB
    @1
    wss
    #
    @23
    @26
    @5
    cB
    cA
    ssun2
    #
    a1i
    vx
    cG
    @8
    @1
    @12
    cB
    cR
    cV
    cE
    cD
    pwssplit4.e
    pwssplit4.d
    pwssplit4.g
    @8
    eqid
    #
    @12
    eqid
    pwssplit3
    syld3an3
    @5
    cK
    @17
    cC
    c0g
    cfv
    #
    wceq
    #
    vy
    cG
    crab
    #
    @24
    @5
    cK
    @21
    @31
    pwssplit4.k
    @5
    @20
    @30
    vy
    cG
    @5
    @19
    @29
    @17
    @5
    cR
    cmnd
    wcel
    #
    cA
    cvv
    wcel
    #
    @19
    @29
    wceq
    @5
    @0
    cR
    cgrp
    wcel
    @32
    @0
    @2
    @4
    simp1
    #
    cR
    lmodgrp
    cR
    grpmnd
    3syl
    #
    @2
    @0
    @33
    @4
    cA
    @1
    wss
    #
    @2
    @33
    cA
    cB
    ssun1
    #
    cA
    @1
    cV
    ssexg
    mpan
    3ad2ant2
    cR
    cA
    cvv
    cC
    c.0
    pwssplit4.c
    pwssplit4.z
    pws0g
    syl2anc
    eqeq2d
    rabbidv
    syl5eq
    @5
    vy
    cG
    @17
    cmpt
    #
    cE
    cC
    clmhm
    co
    wcel
    #
    @31
    @24
    wcel
    @0
    @2
    @4
    @36
    @39
    @36
    @5
    @37
    a1i
    vy
    cG
    cC
    cbs
    cfv
    #
    @1
    @38
    cA
    cR
    cV
    cE
    cC
    pwssplit4.e
    pwssplit4.c
    pwssplit4.g
    @40
    eqid
    @38
    eqid
    #
    pwssplit3
    syld3an3
    cE
    cC
    @24
    @38
    @31
    @29
    @38
    ccnv
    @29
    csn
    cima
    #
    @31
    @29
    cvv
    wcel
    @42
    @31
    wceq
    cC
    c0g
    fvex
    vy
    cG
    @17
    @29
    @38
    cvv
    @41
    mptiniseg
    ax-mp
    eqcomi
    @29
    eqid
    @24
    eqid
    #
    lmhmkerlss
    syl
    eqeltrd
    #
    cL
    cE
    cD
    @24
    @12
    cK
    @43
    pwssplit4.l
    reslmhm
    syl2anc
    syl5eqel
    #
    @5
    cK
    @8
    cF
    wf1
    #
    cF
    crn
    #
    @8
    wceq
    @9
    @5
    @46
    va
    cv
    #
    cF
    cfv
    #
    cD
    c0g
    cfv
    #
    wceq
    #
    @48
    cL
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    va
    cK
    wral
    #
    @5
    @54
    va
    cK
    @5
    @48
    cK
    wcel
    #
    wa
    @51
    @48
    cB
    cres
    #
    cB
    @18
    cxp
    #
    wceq
    #
    @53
    @56
    @5
    @49
    @57
    @50
    @58
    vx
    cK
    cF
    cB
    @48
    pwssplit4.f
    fvtresfn
    @5
    @58
    @50
    @5
    @32
    cB
    cvv
    wcel
    #
    @58
    @50
    wceq
    @35
    @2
    @0
    @60
    @4
    @26
    @2
    @60
    @27
    cB
    @1
    cV
    ssexg
    mpan
    3ad2ant2
    #
    cR
    cB
    cvv
    cD
    c.0
    pwssplit4.d
    pwssplit4.z
    pws0g
    syl2anc
    eqcomd
    eqeqan12rd
    @5
    @56
    @59
    @53
    wi
    #
    @56
    @48
    cG
    wcel
    #
    @48
    cA
    cres
    #
    @19
    wceq
    #
    wa
    #
    @5
    @62
    @20
    @65
    vy
    @48
    cG
    cK
    @16
    @48
    wceq
    @17
    @64
    @19
    @16
    @48
    cA
    reseq1
    eqeq1d
    pwssplit4.k
    elrab2
    @5
    @66
    @59
    @53
    @5
    @66
    @59
    wa
    #
    wa
    #
    @48
    @1
    cres
    #
    @1
    @18
    cxp
    #
    @48
    @52
    @67
    @69
    @70
    wceq
    #
    @5
    @65
    @59
    @71
    @63
    @65
    @59
    wa
    @64
    @57
    cun
    @19
    @58
    cun
    @69
    @70
    @64
    @19
    @57
    @58
    uneq12
    @48
    cA
    cB
    resundi
    cA
    cB
    @18
    xpundir
    3eqtr4g
    adantll
    adantl
    @68
    @1
    cR
    cbs
    cfv
    #
    @48
    wf
    @48
    @1
    wfn
    @69
    @48
    wceq
    @68
    @72
    cR
    @1
    cG
    clmod
    @48
    cE
    cV
    pwssplit4.e
    @72
    eqid
    #
    pwssplit4.g
    @0
    @2
    @4
    @67
    simpl1
    @5
    @2
    @67
    @0
    @2
    @4
    simp2
    #
    adantr
    @5
    @63
    @65
    @59
    simprll
    pwselbas
    @1
    @72
    @48
    ffn
    @1
    @48
    fnresdm
    3syl
    @5
    @70
    @52
    wceq
    @67
    @5
    @70
    cE
    c0g
    cfv
    #
    @52
    @5
    @32
    @2
    @70
    @75
    wceq
    @35
    @74
    cR
    @1
    cV
    cE
    c.0
    pwssplit4.e
    pwssplit4.z
    pws0g
    syl2anc
    @5
    cK
    cE
    csubg
    cfv
    wcel
    #
    @75
    @52
    wceq
    @5
    cE
    clmod
    wcel
    #
    @25
    @76
    @0
    @2
    @77
    @4
    cR
    @1
    cV
    cE
    pwssplit4.e
    pwslmod
    3adant3
    @44
    @24
    cK
    cE
    @43
    lsssubg
    syl2anc
    cK
    cE
    cL
    @75
    pwssplit4.l
    @75
    eqid
    subg0
    syl
    eqtrd
    adantr
    3eqtr3d
    exp32
    syl5bi
    imp
    sylbid
    ralrimiva
    @5
    @7
    cF
    cL
    cD
    cghm
    co
    wcel
    @46
    @55
    wb
    @45
    cL
    cD
    cF
    lmghm
    va
    cL
    cD
    @50
    cF
    cK
    @8
    @52
    @15
    cK
    cL
    cbs
    cfv
    #
    wceq
    @22
    cK
    cG
    cL
    cE
    pwssplit4.l
    pwssplit4.g
    ressbas2
    ax-mp
    #
    @28
    @52
    eqid
    @50
    eqid
    ghmf1
    3syl
    mpbird
    @5
    @47
    @8
    @5
    @7
    @78
    @8
    cF
    wf
    @47
    @8
    wss
    @45
    @78
    @8
    cL
    cD
    cF
    @78
    eqid
    @28
    lmhmf
    @78
    @8
    cF
    frn
    3syl
    @5
    va
    @8
    @47
    @5
    @48
    @8
    wcel
    #
    @48
    @47
    wcel
    @5
    @80
    wa
    #
    @48
    @19
    cun
    #
    cF
    cfv
    #
    @48
    @47
    @81
    @83
    @82
    cB
    cres
    #
    @48
    @81
    @82
    cK
    wcel
    #
    @84
    cvv
    wcel
    #
    @83
    @84
    wceq
    @81
    @82
    cG
    wcel
    #
    @82
    cA
    cres
    #
    @19
    wceq
    #
    @85
    @81
    @87
    @1
    @72
    @82
    wf
    #
    @81
    cB
    cA
    cun
    #
    @72
    @72
    cun
    #
    @82
    wf
    #
    @90
    @81
    cB
    @72
    @48
    wf
    #
    cA
    @72
    @19
    wf
    cB
    cA
    cin
    #
    c0
    wceq
    #
    @93
    @5
    @80
    @94
    @5
    @0
    @60
    @80
    @94
    wb
    @34
    @61
    @72
    cR
    cB
    @8
    clmod
    @48
    cD
    cvv
    pwssplit4.d
    @73
    @28
    pwselbasb
    syl2anc
    biimpa
    #
    @81
    cA
    @18
    @72
    @19
    cA
    @18
    @19
    wf
    #
    @81
    cA
    c.0
    c.0
    cR
    c0g
    cfv
    cvv
    pwssplit4.z
    cR
    c0g
    fvex
    eqeltri
    #
    fconst
    #
    a1i
    @81
    c.0
    @72
    @81
    @32
    c.0
    @72
    wcel
    @5
    @32
    @80
    @35
    adantr
    @72
    cR
    c.0
    @73
    pwssplit4.z
    mndidcl
    syl
    snssd
    fssd
    @5
    @96
    @80
    @5
    @95
    @3
    c0
    cB
    cA
    incom
    #
    @0
    @2
    @4
    simp3
    syl5eq
    adantr
    cB
    cA
    @72
    @72
    @48
    @19
    fun
    syl21anc
    @91
    @92
    @1
    @72
    @82
    cB
    cA
    uncom
    @72
    unidm
    feq23i
    sylib
    @5
    @87
    @90
    wb
    #
    @80
    @0
    @2
    @102
    @4
    @72
    cR
    @1
    cG
    clmod
    @82
    cE
    cV
    pwssplit4.e
    @73
    pwssplit4.g
    pwselbasb
    3adant3
    adantr
    mpbird
    @81
    @64
    @19
    cA
    cres
    #
    cun
    c0
    @19
    cun
    #
    @88
    @19
    @81
    @64
    c0
    @103
    @19
    @81
    @96
    @64
    c0
    wceq
    #
    @81
    @95
    @3
    c0
    @101
    @0
    @2
    @4
    @80
    simpl3
    syl5eq
    @81
    @94
    @48
    cB
    wfn
    #
    @96
    @105
    wb
    @97
    cB
    @72
    @48
    ffn
    #
    cB
    cA
    @48
    fnresdisj
    3syl
    mpbid
    @103
    @19
    wceq
    #
    @81
    c.0
    cvv
    wcel
    @19
    cA
    wfn
    #
    @108
    @99
    cA
    c.0
    cvv
    fnconstg
    cA
    @19
    fnresdm
    mp2b
    a1i
    uneq12d
    @48
    @19
    cA
    resundir
    @104
    @19
    c0
    cun
    @19
    c0
    @19
    uncom
    @19
    un0
    eqtr2i
    3eqtr4g
    @20
    @89
    vy
    @82
    cG
    cK
    @16
    @82
    wceq
    @17
    @88
    @19
    @16
    @82
    cA
    reseq1
    eqeq1d
    pwssplit4.k
    elrab2
    sylanbrc
    #
    @81
    @85
    @86
    @110
    @82
    cB
    cK
    resexg
    syl
    vx
    @82
    @11
    @84
    cK
    cvv
    cF
    @10
    @82
    cB
    reseq1
    pwssplit4.f
    fvmptg
    syl2anc
    @81
    @84
    @57
    @19
    cB
    cres
    #
    cun
    #
    @48
    @48
    @19
    cB
    resundir
    @81
    @112
    @48
    c0
    cun
    @48
    @81
    @57
    @48
    @111
    c0
    @81
    @94
    @106
    @57
    @48
    wceq
    @97
    @107
    cB
    @48
    fnresdm
    3syl
    @5
    @111
    c0
    wceq
    #
    @80
    @4
    @0
    @113
    @2
    @4
    @113
    @98
    @109
    @4
    @113
    wb
    @100
    cA
    @18
    @19
    ffn
    cA
    cB
    @19
    fnresdisj
    mp2b
    biimpi
    3ad2ant3
    adantr
    uneq12d
    @48
    un0
    syl6eq
    syl5eq
    eqtrd
    @81
    cF
    cK
    wfn
    #
    @85
    @83
    @47
    wcel
    @5
    @114
    @80
    @5
    @7
    cK
    @8
    cF
    wf
    @114
    @45
    cK
    @8
    cL
    cD
    cF
    @79
    @28
    lmhmf
    cK
    @8
    cF
    ffn
    3syl
    adantr
    @110
    cK
    @82
    cF
    fnfvelrn
    syl2anc
    eqeltrrd
    ex
    ssrdv
    eqssd
    cK
    @8
    cF
    dff1o5
    sylanbrc
    cK
    @8
    cL
    cD
    cF
    @79
    @28
    islmim
    sylanbrc
end
