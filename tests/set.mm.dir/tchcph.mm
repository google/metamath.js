include "cphl.mm"
include "wcel.mm"
include "cnlm.mm"
include "ccnfld.mm"
include "cbs.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "csqrt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cin.mm"
include "cima.mm"
include "wss.mm"
include "cnm.mm"
include "cv.mm"
include "cmpt.mm"
include "ccph.mm"
include "tchphl.mm"
include "sylib.mm"
include "cngp.mm"
include "clmod.mm"
include "cnrg.mm"
include "cvsca.mm"
include "cmul.mm"
include "wral.mm"
include "csg.mm"
include "c0g.mm"
include "tchval.mm"
include "eqid.mm"
include "cgrp.mm"
include "phllmod.mm"
include "syl.mm"
include "lmodgrp.mm"
include "cr.mm"
include "wa.mm"
include "tchcphlem3.mm"
include "resqrtcld.mm"
include "fmptd.mm"
include "oveq12.mm"
include "anidms.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt3i.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "c2.mm"
include "cexp.mm"
include "cc.mm"
include "wb.mm"
include "csubrg.mm"
include "clvec.mm"
include "cdr.mm"
include "phllvec.mm"
include "lvecdrng.mm"
include "cphsubrglem.mm"
include "simp2d.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "adantr.mm"
include "ipcl.mm"
include "3anidm23.mm"
include "sylan.mm"
include "sseldd.mm"
include "sqrtcld.mm"
include "sqeq0.mm"
include "sqsqrtd.mm"
include "cclm.mm"
include "tchclm.mm"
include "clm0.mm"
include "eqeq12d.mm"
include "bitr3d.mm"
include "ipeq0.mm"
include "3bitrd.mm"
include "caddc.mm"
include "cle.mm"
include "simp1d.mm"
include "wbr.mm"
include "3anass.mm"
include "simpr2.mm"
include "recnd.mm"
include "jca.mm"
include "ex.mm"
include "eleq2d.mm"
include "recn.mm"
include "elin.mm"
include "rbaib.mm"
include "sylan9bb.mm"
include "adantrr.mm"
include "pm5.32rd.mm"
include "syl6bbr.mm"
include "syl6bb.mm"
include "3imtr4d.mm"
include "syl5bi.mm"
include "imp.mm"
include "adantlr.mm"
include "simprl.mm"
include "simprr.mm"
include "tchcphlem1.mm"
include "grpsubcl.mm"
include "3expb.mm"
include "oveqan12d.mm"
include "3brtr4d.mm"
include "tngngpd.mm"
include "cnnrg.mm"
include "simp3d.mm"
include "subrgnrg.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "3jca.mm"
include "cabs.mm"
include "tchcphlem2.mm"
include "lmodvscl.mm"
include "tchnmval.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "cnfldnm.mm"
include "subgnm2.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "tchbas.mm"
include "tchvsca.mm"
include "tchsca.mm"
include "isnlm.mm"
include "sylanbrc.mm"
include "elrege0.mm"
include "anbi2i.mm"
include "bitri.mm"
include "ralrimiv.mm"
include "wfun.mm"
include "cdm.mm"
include "wf.mm"
include "sqrtf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "inss1.mm"
include "syl5ss.mm"
include "fdmi.mm"
include "syl6sseqr.mm"
include "funimass4.mm"
include "mpbird.mm"
include "cnex.mm"
include "tngnm.mm"
include "eqcomd.mm"
include "tchip.mm"
include "iscph.mm"
include "syl3anbrc.mm"

theorem tchcph
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cG: class G
  let c.xi: class .,
  let cK: class K
  let cV: class V
  let cW: class W
  let c.mi: class .-
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchcph.v: |- V = ( Base ` W )
  assume tchcph.f: |- F = ( Scalar ` W )
  assume tchcph.1: |- ( ph -> W e. PreHil )
  assume tchcph.2: |- ( ph -> F = ( CCfld |`s K ) )
  assume tchcph.h: |- ., = ( .i ` W )
  assume tchcph.3: |- ( ( ph /\ ( x e. K /\ x e. RR /\ 0 <_ x ) ) -> ( sqrt ` x ) e. K )
  assume tchcph.4: |- ( ( ph /\ x e. V ) -> 0 <_ ( x ., x ) )

  disjoint ., x
  disjoint F x
  disjoint G x
  disjoint V x
  disjoint ph x
  disjoint W x
  disjoint .- x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ., w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ., y
  disjoint ., z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint C x
  disjoint ph y
  disjoint ph z
  disjoint W w
  disjoint W y
  disjoint W z
  disjoint .x. x
  disjoint X x
  disjoint Y x
  assert |- ( ph -> G e. CPreHil )

  proof
    wph
    cG
    cphl
    wcel
    #
    cG
    cnlm
    wcel
    #
    cF
    ccnfld
    cF
    cbs
    cfv
    #
    cress
    co
    #
    wceq
    #
    w3a
    csqrt
    @2
    cc0
    cpnf
    cico
    co
    #
    cin
    #
    cima
    @2
    wss
    #
    cG
    cnm
    cfv
    #
    vy
    cV
    vy
    cv
    #
    @9
    c.xi
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    wceq
    cG
    ccph
    wcel
    wph
    @0
    @1
    @4
    wph
    cW
    cphl
    wcel
    #
    @0
    tchcph.1
    cG
    cW
    tchval.n
    tchphl
    sylib
    #
    wph
    cG
    cngp
    wcel
    #
    cG
    clmod
    wcel
    #
    cF
    cnrg
    wcel
    #
    w3a
    @9
    vz
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    @8
    cfv
    #
    @9
    cF
    cnm
    cfv
    #
    cfv
    #
    @18
    @8
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vz
    cV
    wral
    vy
    @2
    wral
    @1
    wph
    @15
    @16
    @17
    wph
    vy
    vz
    cG
    cW
    cW
    csg
    cfv
    #
    vx
    cV
    vx
    cv
    #
    @28
    c.xi
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    cV
    cW
    c0g
    cfv
    #
    vx
    cG
    c.xi
    cV
    cW
    tchval.n
    tchcph.v
    tchcph.h
    tchval
    tchcph.v
    @27
    eqid
    #
    @32
    eqid
    #
    wph
    cW
    clmod
    wcel
    #
    cW
    cgrp
    wcel
    #
    wph
    @13
    @35
    tchcph.1
    cW
    phllmod
    syl
    #
    cW
    lmodgrp
    syl
    #
    wph
    vx
    cV
    @30
    cr
    @31
    wph
    @28
    cV
    wcel
    #
    wa
    @29
    wph
    cF
    cG
    c.xi
    cK
    cV
    cW
    @28
    tchval.n
    tchcph.v
    tchcph.f
    tchcph.1
    tchcph.2
    tchcph.h
    tchcphlem3
    tchcph.4
    resqrtcld
    @31
    eqid
    #
    fmptd
    wph
    @9
    cV
    wcel
    #
    wa
    #
    @9
    @31
    cfv
    #
    cc0
    wceq
    @11
    cc0
    wceq
    #
    @10
    cF
    c0g
    cfv
    #
    wceq
    #
    @9
    @32
    wceq
    #
    @42
    @43
    @11
    cc0
    @41
    @43
    @11
    wceq
    wph
    vx
    @9
    @30
    @11
    cV
    @31
    @28
    @9
    wceq
    #
    @29
    @10
    csqrt
    @48
    @29
    @10
    wceq
    @28
    @9
    @28
    @9
    c.xi
    oveq12
    anidms
    fveq2d
    @40
    @29
    csqrt
    fvex
    #
    fvmpt3i
    #
    adantl
    eqeq1d
    @42
    @11
    c2
    cexp
    co
    #
    cc0
    wceq
    #
    @44
    @46
    @42
    @11
    cc
    wcel
    @52
    @44
    wb
    @42
    @10
    @42
    @2
    cc
    @10
    wph
    @2
    cc
    wss
    @41
    wph
    @2
    cK
    cc
    cin
    #
    cc
    wph
    @4
    @2
    @53
    wceq
    #
    @2
    ccnfld
    csubrg
    cfv
    wcel
    #
    wph
    cK
    cF
    @2
    @2
    eqid
    #
    tchcph.2
    wph
    cW
    clvec
    wcel
    #
    cF
    cdr
    wcel
    wph
    @13
    @57
    tchcph.1
    cW
    phllvec
    syl
    cF
    cW
    tchcph.f
    lvecdrng
    syl
    cphsubrglem
    #
    simp2d
    #
    cK
    cc
    inss2
    syl6eqss
    #
    adantr
    wph
    @13
    @41
    @10
    @2
    wcel
    #
    tchcph.1
    @13
    @41
    @61
    @9
    @9
    cF
    c.xi
    @2
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    @56
    ipcl
    3anidm23
    sylan
    sseldd
    #
    sqrtcld
    #
    @11
    sqeq0
    syl
    @42
    @51
    @10
    cc0
    @45
    @42
    @10
    @62
    sqsqrtd
    wph
    cc0
    @45
    wceq
    #
    @41
    wph
    cW
    cclm
    wcel
    @64
    wph
    cF
    cG
    cK
    cV
    cW
    tchval.n
    tchcph.v
    tchcph.f
    tchcph.1
    tchcph.2
    tchclm
    cF
    cW
    tchcph.f
    clm0
    syl
    adantr
    eqeq12d
    bitr3d
    wph
    @13
    @41
    @46
    @47
    wb
    tchcph.1
    @9
    cF
    c.xi
    cV
    cW
    @32
    @45
    tchcph.f
    tchcph.h
    tchcph.v
    @45
    eqid
    @34
    ipeq0
    sylan
    3bitrd
    wph
    @41
    @18
    cV
    wcel
    #
    wa
    #
    wa
    #
    @9
    @18
    @27
    co
    #
    @68
    c.xi
    co
    #
    csqrt
    cfv
    #
    @11
    @18
    @18
    c.xi
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    @68
    @31
    cfv
    #
    @43
    @18
    @31
    cfv
    #
    caddc
    co
    #
    cle
    @67
    vx
    cF
    cG
    c.xi
    @2
    @27
    cV
    cW
    @9
    @18
    tchval.n
    tchcph.v
    tchcph.f
    wph
    @13
    @66
    tchcph.1
    adantr
    wph
    @4
    @66
    wph
    @4
    @54
    @55
    @58
    simp1d
    #
    adantr
    tchcph.h
    wph
    @28
    @2
    wcel
    #
    @28
    cr
    wcel
    #
    cc0
    @28
    cle
    wbr
    #
    w3a
    #
    @28
    csqrt
    cfv
    #
    @2
    wcel
    #
    @66
    wph
    @81
    @83
    @81
    @78
    @79
    @80
    wa
    #
    wa
    #
    wph
    @83
    @78
    @79
    @80
    3anass
    wph
    @28
    cK
    wcel
    #
    @79
    @80
    w3a
    #
    @82
    cK
    wcel
    #
    @82
    cc
    wcel
    #
    wa
    #
    @85
    @83
    wph
    @87
    @90
    wph
    @87
    wa
    #
    @88
    @89
    tchcph.3
    @91
    @28
    @91
    @28
    wph
    @86
    @79
    @80
    simpr2
    recnd
    sqrtcld
    jca
    ex
    wph
    @85
    @86
    @84
    wa
    @87
    wph
    @84
    @78
    @86
    wph
    @84
    @78
    @86
    wb
    #
    wph
    @79
    @92
    @80
    wph
    @78
    @28
    @53
    wcel
    #
    @79
    @86
    wph
    @2
    @53
    @28
    @59
    eleq2d
    @79
    @28
    cc
    wcel
    #
    @93
    @86
    wb
    @28
    recn
    @93
    @86
    @94
    @28
    cK
    cc
    elin
    rbaib
    syl
    sylan9bb
    adantrr
    ex
    pm5.32rd
    @86
    @79
    @80
    3anass
    syl6bbr
    wph
    @83
    @82
    @53
    wcel
    @90
    wph
    @2
    @53
    @82
    @59
    eleq2d
    @82
    cK
    cc
    elin
    syl6bb
    3imtr4d
    #
    syl5bi
    imp
    #
    adantlr
    wph
    @39
    cc0
    @29
    cle
    wbr
    #
    @66
    tchcph.4
    adantlr
    @56
    @33
    wph
    @41
    @65
    simprl
    wph
    @41
    @65
    simprr
    tchcphlem1
    @67
    @68
    cV
    wcel
    #
    @74
    @70
    wceq
    wph
    @36
    @66
    @98
    @38
    @36
    @41
    @65
    @98
    cV
    cW
    @27
    @9
    @18
    tchcph.v
    @33
    grpsubcl
    3expb
    sylan
    vx
    @68
    @30
    @70
    cV
    @31
    @28
    @68
    wceq
    #
    @29
    @69
    csqrt
    @99
    @29
    @69
    wceq
    @28
    @68
    @28
    @68
    c.xi
    oveq12
    anidms
    fveq2d
    @40
    @49
    fvmpt3i
    syl
    @66
    @76
    @73
    wceq
    wph
    @41
    @65
    @43
    @11
    @75
    @72
    caddc
    @50
    vx
    @18
    @30
    @72
    cV
    @31
    @28
    @18
    wceq
    #
    @29
    @71
    csqrt
    @100
    @29
    @71
    wceq
    @28
    @18
    @28
    @18
    c.xi
    oveq12
    anidms
    fveq2d
    @40
    @49
    fvmpt3i
    oveqan12d
    adantl
    3brtr4d
    tngngpd
    wph
    @0
    @16
    @14
    cG
    phllmod
    syl
    wph
    cF
    @3
    cnrg
    @77
    wph
    ccnfld
    cnrg
    wcel
    @55
    @3
    cnrg
    wcel
    cnnrg
    wph
    @4
    @54
    @55
    @58
    simp3d
    #
    @2
    ccnfld
    @3
    @3
    eqid
    #
    subrgnrg
    sylancr
    eqeltrd
    3jca
    wph
    @26
    vy
    vz
    @2
    cV
    wph
    @9
    @2
    wcel
    #
    @65
    wa
    #
    wa
    #
    @20
    @20
    c.xi
    co
    csqrt
    cfv
    #
    @9
    cabs
    cfv
    #
    @72
    cmul
    co
    @21
    @25
    @105
    vx
    @19
    cF
    cG
    c.xi
    @2
    cV
    cW
    @9
    @18
    tchval.n
    tchcph.v
    tchcph.f
    wph
    @13
    @104
    tchcph.1
    adantr
    wph
    @4
    @104
    @77
    adantr
    #
    tchcph.h
    wph
    @81
    @83
    @104
    @96
    adantlr
    wph
    @39
    @97
    @104
    tchcph.4
    adantlr
    @56
    @19
    eqid
    #
    wph
    @103
    @65
    simprl
    #
    wph
    @103
    @65
    simprr
    #
    tchcphlem2
    @105
    @36
    @20
    cV
    wcel
    #
    @21
    @106
    wceq
    wph
    @36
    @104
    @38
    adantr
    #
    wph
    @35
    @104
    @112
    @37
    @35
    @103
    @65
    @112
    @9
    @19
    cF
    @2
    cV
    cW
    @18
    tchcph.v
    tchcph.f
    @109
    @56
    lmodvscl
    3expb
    sylan
    cG
    c.xi
    @8
    cV
    cW
    @20
    tchval.n
    @8
    eqid
    #
    tchcph.v
    tchcph.h
    tchnmval
    syl2anc
    @105
    @23
    @107
    @24
    @72
    cmul
    @105
    @23
    @9
    @3
    cnm
    cfv
    #
    cfv
    #
    @107
    @105
    @9
    @22
    @115
    @105
    cF
    @3
    cnm
    @108
    fveq2d
    fveq1d
    @105
    @2
    ccnfld
    csubg
    cfv
    wcel
    #
    @103
    @116
    @107
    wceq
    wph
    @117
    @104
    wph
    @55
    @117
    @101
    @2
    ccnfld
    subrgsubg
    syl
    adantr
    @110
    @2
    ccnfld
    @3
    @115
    cabs
    @9
    @102
    cnfldnm
    @115
    eqid
    subgnm2
    syl2anc
    eqtrd
    @105
    @36
    @65
    @24
    @72
    wceq
    @113
    @111
    cG
    c.xi
    @8
    cV
    cW
    @18
    tchval.n
    @114
    tchcph.v
    tchcph.h
    tchnmval
    syl2anc
    oveq12d
    3eqtr4d
    ralrimivva
    vy
    vz
    @22
    @19
    cF
    @2
    @8
    cV
    cG
    cG
    cV
    cW
    tchval.n
    tchcph.v
    tchbas
    #
    @114
    @19
    cG
    cW
    tchval.n
    @109
    tchvsca
    cF
    cG
    cW
    tchval.n
    tchcph.f
    tchsca
    #
    @56
    @22
    eqid
    isnlm
    sylanbrc
    @77
    3jca
    wph
    @7
    @83
    vx
    @6
    wral
    #
    wph
    @83
    vx
    @6
    @28
    @6
    wcel
    #
    @85
    wph
    @83
    @121
    @78
    @28
    @5
    wcel
    #
    wa
    @85
    @28
    @2
    @5
    elin
    @122
    @84
    @78
    @28
    elrege0
    anbi2i
    bitri
    @95
    syl5bi
    ralrimiv
    wph
    csqrt
    wfun
    #
    @6
    csqrt
    cdm
    #
    wss
    @7
    @120
    wb
    cc
    cc
    csqrt
    wf
    @123
    sqrtf
    cc
    cc
    csqrt
    ffun
    ax-mp
    wph
    @6
    cc
    @124
    wph
    @6
    @2
    cc
    @2
    @5
    inss1
    @60
    syl5ss
    cc
    cc
    csqrt
    sqrtf
    fdmi
    syl6sseqr
    vx
    @6
    @2
    csqrt
    funimass4
    sylancr
    mpbird
    wph
    @12
    @8
    wph
    @36
    cV
    cc
    @12
    wf
    @12
    @8
    wceq
    @38
    wph
    vy
    cV
    @11
    cc
    @12
    @63
    @12
    eqid
    fmptd
    cc
    cG
    cW
    @12
    cV
    vy
    cG
    c.xi
    cV
    cW
    tchval.n
    tchcph.v
    tchcph.h
    tchval
    tchcph.v
    cnex
    tngnm
    syl2anc
    eqcomd
    vy
    cF
    c.xi
    @2
    @8
    cV
    cG
    @118
    c.xi
    cG
    cW
    tchval.n
    tchcph.h
    tchip
    @114
    @119
    @56
    iscph
    syl3anbrc
end
