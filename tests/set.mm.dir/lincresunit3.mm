include "cpw.mm"
include "wcel.mm"
include "clmod.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cbs.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "wf.mm"
include "wa.mm"
include "simp1.mm"
include "3simpa.mm"
include "3ad2ant2.mm"
include "jca.mm"
include "eldifi.mm"
include "lincresunitlem2.mm"
include "syl2an.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "difexg.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "wi.mm"
include "wss.mm"
include "elpwi.mm"
include "ssdifss.mm"
include "a1i.mm"
include "syl5com.mm"
include "impcom.mm"
include "adantl.mm"
include "elpwg.mm"
include "syl.mm"
include "expcom.mm"
include "pweqi.mm"
include "eleq2s.mm"
include "imp.mm"
include "3adant2.mm"
include "lincval.mm"
include "syl3anc.mm"
include "cres.mm"
include "cplusg.mm"
include "simp3.mm"
include "3jca.mm"
include "adantr.mm"
include "3simpb.mm"
include "eqidd.mm"
include "eqid.mm"
include "lincdifsn.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "oveq2d.mm"
include "lincresunit3lem2.mm"
include "eqtr2d.mm"
include "oveq1d.mm"
include "cminusg.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "syl2anr.mm"
include "sselda.mm"
include "lmodvscl.mm"
include "lmodfgrp.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ccmn.mm"
include "lmodcmn.mm"
include "simpll2.mm"
include "lincresunit1.mm"
include "3adantr3.mm"
include "ffvelrnda.mm"
include "ssel2.mm"
include "c0g.mm"
include "syl6sseq.mm"
include "lincresunit2.mm"
include "syl6breq.mm"
include "scmfsupp.mm"
include "syl6breqr.mm"
include "gsumcl.mm"
include "grpinvid2.mm"
include "lmodvsneg.mm"
include "simpr2.mm"
include "lincresunit3lem3.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "syl31anc.mm"
include "biimpd.mm"
include "sylbid.mm"
include "sylbird.mm"
include "3impia.mm"
include "eqtrd.mm"

theorem lincresunit3
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  assume lincresunit.b: |- B = ( Base ` M )
  assume lincresunit.r: |- R = ( Scalar ` M )
  assume lincresunit.e: |- E = ( Base ` R )
  assume lincresunit.u: |- U = ( Unit ` R )
  assume lincresunit.0: |- .0. = ( 0g ` R )
  assume lincresunit.z: |- Z = ( 0g ` M )
  assume lincresunit.n: |- N = ( invg ` R )
  assume lincresunit.i: |- I = ( invr ` R )
  assume lincresunit.t: |- .x. = ( .r ` R )
  assume lincresunit.g: |- G = ( s e. ( S \ { X } ) |-> ( ( I ` ( N ` ( F ` X ) ) ) .x. ( F ` s ) ) )

  disjoint B s
  disjoint E s
  disjoint F s
  disjoint M s
  disjoint S s
  disjoint X s
  disjoint U s
  disjoint I s
  disjoint N s
  disjoint .x. s
  disjoint .0. s
  disjoint G s
  disjoint R s
  disjoint Z s
  disjoint s z
  disjoint B z
  disjoint E z
  disjoint F z
  disjoint G z
  disjoint M z
  disjoint N z
  disjoint R z
  disjoint S z
  disjoint U z
  disjoint X z
  disjoint Z z
  disjoint .0. z
  disjoint k x
  assert |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S ) /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U /\ F finSupp .0. ) /\ ( F ( linC ` M ) S ) = Z ) -> ( G ( linC ` M ) ( S \ { X } ) ) = X )

  proof
    cS
    cB
    cpw
    #
    wcel
    #
    cM
    clmod
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cF
    cE
    cS
    cmap
    co
    wcel
    #
    cX
    cF
    cfv
    #
    cU
    wcel
    #
    cF
    c.0
    cfsupp
    wbr
    #
    w3a
    #
    cF
    cS
    cM
    clinc
    cfv
    #
    co
    #
    cZ
    wceq
    #
    w3a
    #
    cG
    cS
    cX
    csn
    #
    cdif
    #
    @10
    co
    #
    cM
    vs
    @15
    vs
    cv
    #
    cG
    cfv
    #
    @17
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cX
    @13
    @2
    cG
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    @15
    cmap
    co
    wcel
    #
    @15
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    @16
    @22
    wceq
    @4
    @9
    @2
    @12
    @1
    @2
    @3
    simp2
    #
    3ad2ant1
    @13
    @25
    @15
    @24
    cG
    wf
    #
    @13
    vs
    @15
    @6
    cN
    cfv
    #
    cI
    cfv
    @17
    cF
    cfv
    c.x
    co
    #
    @24
    cG
    @13
    @17
    @15
    wcel
    #
    wa
    @32
    cE
    @24
    @13
    @4
    @5
    @7
    wa
    #
    wa
    @17
    cS
    wcel
    #
    @32
    cE
    wcel
    @33
    @13
    @4
    @34
    @4
    @9
    @12
    simp1
    @9
    @4
    @34
    @12
    @5
    @7
    @8
    3simpa
    3ad2ant2
    jca
    @17
    cS
    @14
    eldifi
    #
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    @17
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunitlem2
    syl2an
    cE
    cR
    cbs
    cfv
    @24
    lincresunit.e
    cR
    @23
    cbs
    lincresunit.r
    fveq2i
    eqtri
    syl6eleq
    lincresunit.g
    fmptd
    @13
    @24
    cvv
    wcel
    @15
    cvv
    wcel
    #
    @25
    @30
    wb
    @23
    cbs
    fvex
    @4
    @9
    @37
    @12
    @1
    @2
    @37
    @3
    cS
    @14
    @0
    difexg
    #
    3ad2ant1
    #
    3ad2ant1
    @24
    @15
    cG
    cvv
    cvv
    elmapg
    sylancr
    mpbird
    @4
    @9
    @28
    @12
    @1
    @3
    @28
    @2
    @1
    @3
    @28
    @3
    @28
    wi
    cS
    @27
    @0
    @3
    cS
    @27
    wcel
    #
    @28
    @3
    @40
    wa
    #
    @28
    @15
    @26
    wss
    #
    @40
    @3
    @42
    @40
    cS
    @26
    wss
    #
    @3
    @42
    cS
    @26
    elpwi
    @43
    @42
    wi
    @3
    cS
    @26
    @14
    ssdifss
    a1i
    syl5com
    impcom
    @41
    @37
    @28
    @42
    wb
    #
    @40
    @37
    @3
    cS
    @14
    @27
    difexg
    adantl
    @15
    @26
    cvv
    elpwg
    #
    syl
    mpbird
    expcom
    cB
    @26
    lincresunit.b
    pweqi
    eleq2s
    imp
    3adant2
    3ad2ant1
    vs
    cG
    cM
    @15
    clmod
    lincval
    syl3anc
    @4
    @9
    @12
    @22
    cX
    wceq
    #
    @4
    @9
    wa
    #
    @12
    cF
    @15
    cres
    #
    @15
    @10
    co
    #
    @6
    cX
    @19
    co
    #
    cM
    cplusg
    cfv
    #
    co
    #
    cZ
    wceq
    #
    @46
    @47
    @11
    @52
    cZ
    @47
    @2
    @1
    @3
    w3a
    #
    @5
    @8
    wa
    #
    @48
    @48
    wceq
    @11
    @52
    wceq
    @4
    @54
    @9
    @4
    @2
    @1
    @3
    @29
    @1
    @2
    @3
    simp1
    @1
    @2
    @3
    simp3
    #
    3jca
    adantr
    @9
    @55
    @4
    @5
    @7
    @8
    3simpb
    adantl
    @47
    @48
    eqidd
    cB
    @51
    cR
    cE
    @19
    cF
    @48
    cM
    cS
    cX
    c.0
    lincresunit.b
    lincresunit.r
    lincresunit.e
    @19
    eqid
    #
    @51
    eqid
    #
    lincresunit.0
    lincdifsn
    syl3anc
    eqeq1d
    @47
    @53
    @31
    @22
    @19
    co
    #
    @50
    @51
    co
    #
    cZ
    wceq
    #
    @46
    @47
    @52
    @60
    cZ
    @47
    @49
    @59
    @50
    @51
    @47
    @59
    @31
    cM
    vz
    @15
    vz
    cv
    #
    cG
    cfv
    #
    @62
    @19
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @19
    co
    @49
    @47
    @22
    @66
    @31
    @19
    @47
    @21
    @65
    cM
    cgsu
    @21
    @65
    wceq
    @47
    vs
    vz
    @15
    @20
    @64
    @17
    @62
    wceq
    #
    @18
    @63
    @17
    @62
    @19
    @17
    @62
    cG
    fveq2
    @67
    id
    oveq12d
    cbvmptv
    a1i
    oveq2d
    oveq2d
    vz
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunit3lem2
    eqtr2d
    oveq1d
    eqeq1d
    @47
    @61
    @50
    cM
    cminusg
    cfv
    #
    cfv
    #
    @59
    wceq
    #
    @46
    @47
    cM
    cgrp
    wcel
    #
    @50
    cB
    wcel
    #
    @59
    cB
    wcel
    #
    @70
    @61
    wb
    @4
    @71
    @9
    @2
    @1
    @71
    @3
    cM
    lmodgrp
    3ad2ant2
    adantr
    @47
    @2
    @6
    cE
    wcel
    #
    cX
    cB
    wcel
    #
    @72
    @4
    @2
    @9
    @29
    adantr
    #
    @9
    cS
    cE
    cF
    wf
    #
    @3
    @74
    @4
    @5
    @7
    @77
    @8
    cF
    cE
    cS
    elmapi
    3ad2ant1
    @56
    cS
    cE
    cX
    cF
    ffvelrn
    syl2anr
    #
    @4
    @75
    @9
    @1
    @3
    @75
    @2
    @1
    cS
    cB
    cX
    cS
    cB
    elpwi
    #
    sselda
    3adant2
    adantr
    #
    @6
    @19
    cR
    cE
    cB
    cM
    cX
    lincresunit.b
    lincresunit.r
    @57
    lincresunit.e
    lmodvscl
    syl3anc
    @47
    @2
    @31
    cE
    wcel
    #
    @22
    cB
    wcel
    #
    @73
    @76
    @47
    cR
    cgrp
    wcel
    #
    @74
    @81
    @4
    @83
    @9
    @2
    @1
    @83
    @3
    cR
    cM
    lincresunit.r
    lmodfgrp
    3ad2ant2
    adantr
    @78
    cE
    cR
    cN
    @6
    lincresunit.e
    lincresunit.n
    grpinvcl
    syl2anc
    @47
    @15
    cB
    @21
    cM
    cvv
    cZ
    lincresunit.b
    lincresunit.z
    @4
    cM
    ccmn
    wcel
    #
    @9
    @2
    @1
    @84
    @3
    cM
    lmodcmn
    3ad2ant2
    adantr
    @4
    @37
    @9
    @39
    adantr
    @47
    vs
    @15
    @20
    cB
    @21
    @47
    @33
    wa
    @2
    @18
    cE
    wcel
    @17
    cB
    wcel
    #
    @20
    cB
    wcel
    @1
    @2
    @3
    @9
    @33
    simpll2
    @47
    @15
    cE
    @17
    cG
    @47
    cG
    cE
    @15
    cmap
    co
    wcel
    #
    @15
    cE
    cG
    wf
    @4
    @5
    @7
    @86
    @8
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunit1
    3adantr3
    #
    cG
    cE
    @15
    elmapi
    syl
    ffvelrnda
    @47
    @33
    @85
    @4
    @33
    @85
    wi
    #
    @9
    @1
    @2
    @88
    @3
    @1
    cS
    cB
    wss
    #
    @33
    @85
    @79
    @33
    @35
    @89
    @85
    wi
    @36
    @89
    @35
    @85
    cS
    cB
    @17
    ssel2
    expcom
    syl
    syl5com
    3ad2ant1
    adantr
    imp
    @18
    @19
    cR
    cE
    cB
    cM
    @17
    lincresunit.b
    lincresunit.r
    @57
    lincresunit.e
    lmodvscl
    syl3anc
    @21
    eqid
    fmptd
    @47
    @21
    cM
    c0g
    cfv
    #
    cZ
    cfsupp
    @47
    @2
    @28
    wa
    #
    @86
    cG
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    @21
    @90
    cfsupp
    wbr
    @4
    @91
    @9
    @4
    @2
    @28
    @29
    @1
    @3
    @28
    @2
    @1
    @3
    wa
    #
    @28
    @42
    @93
    @15
    cB
    @26
    @1
    @15
    cB
    wss
    #
    @3
    @1
    @89
    @94
    @79
    cS
    cB
    @14
    ssdifss
    syl
    adantr
    lincresunit.b
    syl6sseq
    @93
    @37
    @44
    @1
    @37
    @3
    @38
    adantr
    @45
    syl
    mpbird
    3adant2
    jca
    adantr
    @87
    @47
    cG
    c.0
    @92
    cfsupp
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunit2
    lincresunit.0
    syl6breq
    vs
    cG
    cE
    cR
    cM
    @15
    lincresunit.r
    lincresunit.e
    scmfsupp
    syl3anc
    lincresunit.z
    syl6breqr
    gsumcl
    #
    @31
    @19
    cR
    cE
    cB
    cM
    @22
    lincresunit.b
    lincresunit.r
    @57
    lincresunit.e
    lmodvscl
    syl3anc
    cB
    @51
    cM
    @68
    @50
    @59
    cZ
    lincresunit.b
    @58
    lincresunit.z
    @68
    eqid
    #
    grpinvid2
    syl3anc
    @47
    @70
    @31
    cX
    @19
    co
    #
    @59
    wceq
    #
    @46
    @47
    @69
    @97
    @59
    @47
    cB
    @6
    @19
    cR
    cE
    cN
    @68
    cM
    cX
    lincresunit.b
    lincresunit.r
    @57
    @96
    lincresunit.e
    lincresunit.n
    @76
    @80
    @78
    lmodvsneg
    eqeq1d
    @47
    @98
    @46
    @47
    @2
    @75
    @82
    @7
    @98
    @46
    wb
    @76
    @80
    @95
    @4
    @5
    @7
    @8
    simpr2
    @2
    @75
    @82
    w3a
    @7
    wa
    @98
    cX
    @22
    wceq
    @46
    @6
    cB
    cR
    @19
    cU
    cE
    cM
    cN
    cX
    @22
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.n
    @57
    lincresunit3lem3
    cX
    @22
    eqcom
    syl6bb
    syl31anc
    biimpd
    sylbid
    sylbird
    sylbid
    sylbid
    3impia
    eqtrd
end
