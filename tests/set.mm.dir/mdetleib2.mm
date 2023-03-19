include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "ccom.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csymg.mm"
include "cminusg.mm"
include "wceq.mm"
include "mdetleib.mm"
include "adantl.mm"
include "cbs.mm"
include "eqid.mm"
include "ccmn.mm"
include "crg.mm"
include "crngring.mm"
include "ringcmn.mm"
include "syl.mm"
include "adantr.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "symgbasfi.mm"
include "ad2antrr.mm"
include "cmgp.mm"
include "cmhm.mm"
include "wf.mm"
include "czrh.mm"
include "cpsgn.mm"
include "coeq12i.mm"
include "zrhpsgnmhm.mm"
include "syl5eqel.mm"
include "syl2anc.mm"
include "mgpbas.mm"
include "mhmf.mm"
include "ffvelrnda.mm"
include "crngmgp.mm"
include "cxp.mm"
include "cmap.mm"
include "simpr.mm"
include "matbas2i.mm"
include "elmapi.mm"
include "3syl.mm"
include "wf1o.mm"
include "symgbasf1o.mm"
include "f1of.mm"
include "fovrnd.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "cgrp.mm"
include "symggrp.mm"
include "grpinvf1o.mm"
include "gsummptfif1o.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "fveq2.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "fmptco.mm"
include "ccnv.mm"
include "symginv.mm"
include "fveq2d.mm"
include "zrhpsgninv.mm"
include "eqtrd.mm"
include "ad2antlr.mm"
include "fveq1d.mm"
include "f1ocnv.mm"
include "eqeltrd.mm"
include "syl6eleq.mm"
include "id.mm"
include "f1ocnvfv1.mm"
include "sylan.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"

theorem mdetleib2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cM: class M
  let cN: class N
  let cY: class Y
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vq: setvar q
  assume mdetfval.d: |- D = ( N maDet R )
  assume mdetfval.a: |- A = ( N Mat R )
  assume mdetfval.b: |- B = ( Base ` A )
  assume mdetfval.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume mdetfval.y: |- Y = ( ZRHom ` R )
  assume mdetfval.s: |- S = ( pmSgn ` N )
  assume mdetfval.t: |- .x. = ( .r ` R )
  assume mdetfval.u: |- U = ( mulGrp ` R )

  disjoint p x
  disjoint M p
  disjoint M x
  disjoint N p
  disjoint N x
  disjoint R p
  disjoint R x
  disjoint B p
  disjoint B x
  disjoint P p
  disjoint P x
  disjoint S p
  disjoint U p
  disjoint Y p
  disjoint .x. p
  disjoint y z
  disjoint m n
  disjoint m r
  disjoint B m
  disjoint n r
  disjoint B n
  disjoint B r
  disjoint m p
  disjoint m x
  disjoint M m
  disjoint N m
  disjoint n p
  disjoint n x
  disjoint N n
  disjoint p r
  disjoint r x
  disjoint N r
  disjoint P m
  disjoint P n
  disjoint P r
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint S m
  disjoint S n
  disjoint S r
  disjoint .x. m
  disjoint .x. n
  disjoint .x. r
  disjoint U m
  disjoint U n
  disjoint U r
  disjoint Y m
  disjoint Y n
  disjoint Y r
  disjoint B q
  disjoint B y
  disjoint p q
  disjoint p y
  disjoint q x
  disjoint q y
  disjoint x y
  disjoint M q
  disjoint M y
  disjoint N q
  disjoint N y
  disjoint P q
  disjoint P y
  disjoint R q
  disjoint R y
  disjoint S q
  disjoint U q
  disjoint U y
  disjoint Y q
  disjoint .x. q
  assert |- ( ( R e. CRing /\ M e. B ) -> ( D ` M ) = ( R gsum ( p e. P |-> ( ( ( Y o. S ) ` p ) .x. ( U gsum ( x e. N |-> ( x M ( p ` x ) ) ) ) ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    cM
    cD
    cfv
    #
    cR
    vq
    cP
    vq
    cv
    #
    cY
    cS
    ccom
    #
    cfv
    #
    cU
    vy
    cN
    vy
    cv
    #
    @4
    cfv
    #
    @7
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    @13
    cN
    csymg
    cfv
    #
    cminusg
    cfv
    #
    ccom
    #
    cgsu
    co
    cR
    vp
    cP
    vp
    cv
    #
    @5
    cfv
    #
    cU
    vx
    cN
    vx
    cv
    #
    @20
    @18
    cfv
    #
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    @1
    @3
    @14
    wceq
    @0
    vy
    cA
    cB
    cD
    cP
    cR
    cS
    c.x
    cU
    cM
    cN
    cY
    vq
    mdetfval.d
    mdetfval.a
    mdetfval.b
    mdetfval.p
    mdetfval.y
    mdetfval.s
    mdetfval.t
    mdetfval.u
    mdetleib
    adantl
    @2
    cR
    cbs
    cfv
    #
    cP
    vq
    @13
    cR
    @16
    cP
    @12
    @27
    eqid
    #
    @0
    cR
    ccmn
    wcel
    #
    @1
    @0
    cR
    crg
    wcel
    #
    @29
    cR
    crngring
    #
    cR
    ringcmn
    syl
    adantr
    @2
    cN
    cfn
    wcel
    #
    cP
    cfn
    wcel
    @2
    @32
    cR
    cvv
    wcel
    #
    @1
    @32
    @33
    wa
    @0
    cA
    cB
    cR
    cN
    cM
    mdetfval.a
    mdetfval.b
    matrcl
    adantl
    simpld
    #
    cN
    cP
    @15
    @15
    eqid
    #
    mdetfval.p
    symgbasfi
    syl
    @2
    @12
    @27
    wcel
    #
    vq
    cP
    @2
    @4
    cP
    wcel
    #
    wa
    #
    @30
    @6
    @27
    wcel
    @11
    @27
    wcel
    @36
    @0
    @30
    @1
    @37
    @31
    ad2antrr
    @2
    cP
    @27
    @4
    @5
    @2
    @5
    @15
    cR
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    #
    cP
    @27
    @5
    wf
    @2
    @30
    @32
    @41
    @0
    @30
    @1
    @31
    adantr
    @34
    @30
    @32
    wa
    @5
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    @40
    cY
    @42
    cS
    @43
    mdetfval.y
    mdetfval.s
    coeq12i
    cN
    cR
    zrhpsgnmhm
    syl5eqel
    syl2anc
    cP
    @27
    @15
    @39
    @5
    mdetfval.p
    @27
    cR
    @39
    @39
    eqid
    @28
    mgpbas
    mhmf
    syl
    ffvelrnda
    @38
    @27
    vy
    cU
    cN
    @9
    @27
    cR
    cU
    mdetfval.u
    @28
    mgpbas
    #
    @0
    cU
    ccmn
    wcel
    #
    @1
    @37
    cR
    cU
    mdetfval.u
    crngmgp
    #
    ad2antrr
    @2
    @32
    @37
    @34
    adantr
    @38
    @9
    @27
    wcel
    vy
    cN
    @38
    @7
    cN
    wcel
    #
    wa
    @8
    @7
    @27
    cN
    cN
    cM
    @2
    cN
    cN
    cxp
    #
    @27
    cM
    wf
    #
    @37
    @47
    @2
    @1
    cM
    @27
    @48
    cmap
    co
    wcel
    @49
    @0
    @1
    simpr
    cA
    cB
    cR
    @27
    cM
    cN
    mdetfval.a
    @28
    mdetfval.b
    matbas2i
    cM
    @27
    @48
    elmapi
    3syl
    #
    ad2antrr
    @38
    cN
    cN
    @7
    @4
    @38
    cN
    cN
    @4
    wf1o
    #
    cN
    cN
    @4
    wf
    @37
    @51
    @2
    cN
    cP
    @4
    @15
    @35
    mdetfval.p
    symgbasf1o
    adantl
    cN
    cN
    @4
    f1of
    syl
    ffvelrnda
    @38
    @47
    simpr
    fovrnd
    ralrimiva
    gsummptcl
    @27
    cR
    c.x
    @6
    @11
    @28
    mdetfval.t
    ringcl
    syl3anc
    ralrimiva
    @13
    eqid
    @2
    cP
    @15
    @16
    mdetfval.p
    @16
    eqid
    #
    @2
    @32
    @15
    cgrp
    wcel
    @34
    cN
    @15
    cfn
    @35
    symggrp
    syl
    grpinvf1o
    #
    gsummptfif1o
    @2
    @17
    @26
    cR
    cgsu
    @2
    @17
    vp
    cP
    @18
    @16
    cfv
    #
    @5
    cfv
    #
    cU
    vy
    cN
    @7
    @54
    cfv
    #
    @7
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    @26
    @2
    vp
    vq
    cP
    cP
    @54
    @12
    @60
    @16
    @13
    @2
    cP
    cP
    @18
    @16
    @2
    cP
    cP
    @16
    wf1o
    cP
    cP
    @16
    wf
    @53
    cP
    cP
    @16
    f1of
    syl
    #
    ffvelrnda
    @2
    vp
    cP
    cP
    @16
    @61
    feqmptd
    @2
    @13
    eqidd
    @4
    @54
    wceq
    #
    @6
    @55
    @11
    @59
    c.x
    @4
    @54
    @5
    fveq2
    @62
    @10
    @58
    cU
    cgsu
    @62
    vy
    cN
    @9
    @57
    @62
    @8
    @56
    @7
    cM
    @7
    @4
    @54
    fveq1
    oveq1d
    mpteq2dv
    oveq2d
    oveq12d
    fmptco
    @2
    vp
    cP
    @60
    @25
    @2
    @18
    cP
    wcel
    #
    wa
    #
    @55
    @19
    @59
    @24
    c.x
    @64
    @55
    @18
    ccnv
    #
    @5
    cfv
    #
    @19
    @64
    @54
    @65
    @5
    @63
    @54
    @65
    wceq
    #
    @2
    cN
    cP
    @18
    @15
    @16
    @35
    mdetfval.p
    @52
    symginv
    #
    adantl
    fveq2d
    @64
    @30
    @32
    @63
    @66
    @19
    wceq
    @0
    @30
    @1
    @63
    @31
    ad2antrr
    @2
    @32
    @63
    @34
    adantr
    #
    @2
    @63
    simpr
    cP
    cR
    cS
    @18
    cN
    cY
    mdetfval.p
    mdetfval.y
    mdetfval.s
    zrhpsgninv
    syl3anc
    eqtrd
    @64
    @59
    cU
    @58
    @18
    ccom
    #
    cgsu
    co
    @24
    @64
    cU
    cbs
    cfv
    #
    cN
    vy
    @58
    cU
    @18
    cN
    @57
    @71
    eqid
    @0
    @45
    @1
    @63
    @46
    ad2antrr
    @69
    @64
    @57
    @71
    wcel
    vy
    cN
    @64
    @47
    wa
    #
    @57
    @27
    @71
    @72
    @56
    @7
    @27
    cN
    cN
    cM
    @2
    @49
    @63
    @47
    @50
    ad2antrr
    @72
    @56
    @7
    @65
    cfv
    cN
    @72
    @7
    @54
    @65
    @63
    @67
    @2
    @47
    @68
    ad2antlr
    fveq1d
    @64
    cN
    cN
    @7
    @65
    @64
    cN
    cN
    @18
    wf1o
    #
    cN
    cN
    @65
    wf1o
    cN
    cN
    @65
    wf
    @63
    @73
    @2
    cN
    cP
    @18
    @15
    @35
    mdetfval.p
    symgbasf1o
    adantl
    #
    cN
    cN
    @18
    f1ocnv
    cN
    cN
    @65
    f1of
    3syl
    ffvelrnda
    eqeltrd
    @64
    @47
    simpr
    fovrnd
    @44
    syl6eleq
    ralrimiva
    @58
    eqid
    @74
    gsummptfif1o
    @64
    @70
    @23
    cU
    cgsu
    @64
    @70
    vx
    cN
    @21
    @54
    cfv
    #
    @21
    cM
    co
    #
    cmpt
    @23
    @64
    vx
    vy
    cN
    cN
    @21
    @57
    @76
    @18
    @58
    @64
    cN
    cN
    @20
    @18
    @64
    @73
    cN
    cN
    @18
    wf
    @74
    cN
    cN
    @18
    f1of
    syl
    #
    ffvelrnda
    @64
    vx
    cN
    cN
    @18
    @77
    feqmptd
    @64
    @58
    eqidd
    @7
    @21
    wceq
    #
    @56
    @75
    @7
    @21
    cM
    @7
    @21
    @54
    fveq2
    @78
    id
    oveq12d
    fmptco
    @64
    vx
    cN
    @76
    @22
    @64
    @20
    cN
    wcel
    #
    wa
    #
    @75
    @20
    @21
    cM
    @80
    @75
    @21
    @65
    cfv
    #
    @20
    @80
    @21
    @54
    @65
    @63
    @67
    @2
    @79
    @68
    ad2antlr
    fveq1d
    @64
    @73
    @79
    @81
    @20
    wceq
    @74
    cN
    cN
    @20
    @18
    f1ocnvfv1
    sylan
    eqtrd
    oveq1d
    mpteq2dva
    eqtrd
    oveq2d
    eqtrd
    oveq12d
    mpteq2dva
    eqtrd
    oveq2d
    3eqtrd
end
