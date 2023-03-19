include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cof.mm"
include "clinc.mm"
include "eqid.mm"
include "ccmn.mm"
include "lmodcmn.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "simpr.mm"
include "simpl.mm"
include "wi.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "imp.mm"
include "elelpwi.mm"
include "expcom.mm"
include "adantl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "eqidd.mm"
include "id.mm"
include "scmfsupp.mm"
include "syl3an.mm"
include "gsummptfsadd.mm"
include "csca.mm"
include "wceq.mm"
include "wfn.mm"
include "elmapfn.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "offvalfv.mm"
include "3adant3.mm"
include "cmnd.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "grpmnd.mm"
include "ad3antrrr.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "eqcomi.mm"
include "mndcl.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "lincval.mm"
include "cplusg.mm"
include "anim12i.mm"
include "anim1i.mm"
include "fnfvof.mm"
include "syl2anc.mm"
include "a1i.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "lmodvsdir.mm"
include "syl13anc.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "oveq12i.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "3eqtr4rd.mm"

theorem lincsum
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cS: class S
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume lincsum.p: |- .+ = ( +g ` M )
  assume lincsum.x: |- X = ( A ( linC ` M ) V )
  assume lincsum.y: |- Y = ( B ( linC ` M ) V )
  assume lincsum.s: |- S = ( Scalar ` M )
  assume lincsum.r: |- R = ( Base ` S )
  assume lincsum.b: |- .+b = ( +g ` S )


  assert |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) /\ ( A e. ( R ^m V ) /\ B e. ( R ^m V ) ) /\ ( A finSupp ( 0g ` S ) /\ B finSupp ( 0g ` S ) ) ) -> ( X .+ Y ) = ( ( A oF .+b B ) ( linC ` M ) V ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    wa
    #
    cA
    cR
    cV
    cmap
    co
    #
    wcel
    #
    cB
    @5
    wcel
    #
    wa
    #
    cA
    cS
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    cB
    @9
    cfsupp
    wbr
    #
    wa
    #
    w3a
    #
    cM
    vx
    cV
    vx
    cv
    #
    cA
    cfv
    #
    @14
    cM
    cvsca
    cfv
    #
    co
    #
    @14
    cB
    cfv
    #
    @14
    @16
    co
    #
    c.pl
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cM
    vx
    cV
    @17
    cmpt
    #
    cgsu
    co
    #
    cM
    vx
    cV
    @19
    cmpt
    #
    cgsu
    co
    #
    c.pl
    co
    #
    cA
    cB
    c.pb
    cof
    co
    #
    cV
    cM
    clinc
    cfv
    #
    co
    #
    cX
    cY
    c.pl
    co
    #
    @13
    vx
    cV
    @1
    @17
    @19
    c.pl
    @23
    cM
    @25
    @2
    cM
    c0g
    cfv
    #
    @1
    eqid
    #
    @32
    eqid
    lincsum.p
    @4
    @8
    cM
    ccmn
    wcel
    #
    @12
    @0
    @34
    @3
    cM
    lmodcmn
    adantr
    3ad2ant1
    @4
    @8
    @3
    @12
    @0
    @3
    simpr
    #
    3ad2ant1
    #
    @13
    @14
    cV
    wcel
    #
    wa
    #
    @0
    @15
    cR
    wcel
    #
    @14
    @1
    wcel
    #
    @17
    @1
    wcel
    @13
    @0
    @37
    @4
    @8
    @0
    @12
    @0
    @3
    simpl
    #
    3ad2ant1
    #
    adantr
    #
    @13
    @37
    @39
    @8
    @4
    @37
    @39
    wi
    #
    @12
    @6
    @44
    @7
    @6
    cV
    cR
    cA
    wf
    #
    @44
    cA
    cR
    cV
    elmapi
    #
    @45
    @37
    @39
    cV
    cR
    @14
    cA
    ffvelrn
    ex
    syl
    #
    adantr
    3ad2ant2
    imp
    @13
    @37
    @40
    @4
    @8
    @37
    @40
    wi
    #
    @12
    @3
    @48
    @0
    @37
    @3
    @40
    @14
    cV
    @1
    elelpwi
    expcom
    adantl
    #
    3ad2ant1
    imp
    #
    @15
    @16
    cS
    cR
    @1
    cM
    @14
    @33
    lincsum.s
    @16
    eqid
    #
    lincsum.r
    lmodvscl
    syl3anc
    @38
    @0
    @18
    cR
    wcel
    #
    @40
    @19
    @1
    wcel
    @43
    @13
    @37
    @52
    @8
    @4
    @37
    @52
    wi
    #
    @12
    @7
    @53
    @6
    @7
    cV
    cR
    cB
    wf
    #
    @53
    cB
    cR
    cV
    elmapi
    #
    @54
    @37
    @52
    cV
    cR
    @14
    cB
    ffvelrn
    ex
    syl
    #
    adantl
    3ad2ant2
    imp
    @50
    @18
    @16
    cS
    cR
    @1
    cM
    @14
    @33
    lincsum.s
    @51
    lincsum.r
    lmodvscl
    syl3anc
    @13
    @23
    eqidd
    @13
    @25
    eqidd
    @4
    @4
    @8
    @6
    @12
    @10
    @23
    @32
    cfsupp
    wbr
    @4
    id
    #
    @6
    @7
    simpl
    @10
    @11
    simpl
    vx
    cA
    cR
    cS
    cM
    cV
    lincsum.s
    lincsum.r
    scmfsupp
    syl3an
    @4
    @4
    @8
    @7
    @12
    @11
    @25
    @32
    cfsupp
    wbr
    @57
    @6
    @7
    simpr
    @10
    @11
    simpr
    vx
    cB
    cR
    cS
    cM
    cV
    lincsum.s
    lincsum.r
    scmfsupp
    syl3an
    gsummptfsadd
    @13
    @30
    cM
    vx
    cV
    @14
    @28
    cfv
    #
    @14
    @16
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @22
    @13
    @0
    @28
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    cV
    cmap
    co
    #
    wcel
    @3
    @30
    @61
    wceq
    @42
    @13
    @28
    vy
    cV
    vy
    cv
    #
    cA
    cfv
    #
    @65
    cB
    cfv
    #
    c.pb
    co
    #
    cmpt
    #
    @64
    @4
    @8
    @28
    @69
    wceq
    @12
    @4
    @8
    wa
    #
    vy
    cV
    c.pb
    cA
    cB
    @2
    @4
    @3
    @8
    @35
    adantr
    #
    @6
    cA
    cV
    wfn
    #
    @4
    @7
    cA
    cR
    cV
    elmapfn
    #
    ad2antrl
    @7
    cB
    cV
    wfn
    #
    @4
    @6
    cB
    cR
    cV
    elmapfn
    #
    ad2antll
    offvalfv
    3adant3
    @4
    @8
    @69
    @64
    wcel
    #
    @12
    @70
    @76
    cV
    @63
    @69
    wf
    #
    @70
    vy
    cV
    @68
    @63
    @69
    @70
    @65
    cV
    wcel
    #
    wa
    #
    cS
    cmnd
    wcel
    #
    @66
    @63
    wcel
    @67
    @63
    wcel
    #
    @68
    @63
    wcel
    @0
    @80
    @3
    @8
    @78
    @0
    cS
    cgrp
    wcel
    @80
    cS
    cM
    lincsum.s
    lmodfgrp
    cS
    grpmnd
    syl
    ad3antrrr
    @79
    @66
    cR
    @63
    @70
    @78
    @66
    cR
    wcel
    #
    @6
    @78
    @82
    wi
    #
    @4
    @7
    @6
    @45
    @83
    @46
    @45
    @78
    @82
    cV
    cR
    @65
    cA
    ffvelrn
    ex
    syl
    ad2antrl
    imp
    cR
    cS
    cbs
    cfv
    @63
    lincsum.r
    cS
    @62
    cbs
    lincsum.s
    fveq2i
    eqtri
    #
    syl6eleq
    @70
    @78
    @81
    @7
    @78
    @81
    wi
    #
    @4
    @6
    @7
    @54
    @85
    @55
    @54
    @78
    @81
    @54
    @78
    wa
    @67
    cR
    @63
    cV
    cR
    @65
    cB
    ffvelrn
    @84
    syl6eleq
    ex
    syl
    ad2antll
    imp
    @63
    c.pb
    cS
    @66
    @67
    @62
    cS
    cbs
    cS
    @62
    lincsum.s
    eqcomi
    fveq2i
    lincsum.b
    mndcl
    syl3anc
    @69
    eqid
    fmptd
    @70
    @63
    cvv
    wcel
    @3
    @76
    @77
    wb
    @62
    cbs
    fvex
    @71
    @63
    cV
    @69
    cvv
    @2
    elmapg
    sylancr
    mpbird
    3adant3
    eqeltrd
    @36
    vx
    @28
    cM
    cV
    clmod
    lincval
    syl3anc
    @4
    @8
    @61
    @22
    wceq
    @12
    @70
    @60
    @21
    cM
    cgsu
    @70
    vx
    cV
    @59
    @20
    @70
    @37
    wa
    #
    @59
    @15
    @18
    cS
    cplusg
    cfv
    #
    co
    #
    @14
    @16
    co
    #
    @20
    @86
    @58
    @88
    @14
    @16
    @86
    @58
    @15
    @18
    c.pb
    co
    #
    @88
    @86
    @72
    @74
    wa
    #
    @3
    @37
    wa
    @58
    @90
    wceq
    @70
    @91
    @37
    @8
    @91
    @4
    @6
    @72
    @7
    @74
    @73
    @75
    anim12i
    adantl
    adantr
    @70
    @3
    @37
    @71
    anim1i
    cV
    c.pb
    cA
    cB
    @2
    @14
    fnfvof
    syl2anc
    @86
    c.pb
    @87
    @15
    @18
    c.pb
    @87
    wceq
    @86
    lincsum.b
    a1i
    oveqd
    eqtrd
    oveq1d
    @86
    @0
    @39
    @52
    @40
    @89
    @20
    wceq
    @70
    @0
    @37
    @4
    @0
    @8
    @41
    adantr
    #
    adantr
    @70
    @37
    @39
    @6
    @44
    @4
    @7
    @47
    ad2antrl
    imp
    @70
    @37
    @52
    @7
    @53
    @4
    @6
    @56
    ad2antll
    imp
    @70
    @37
    @40
    @4
    @48
    @8
    @49
    adantr
    imp
    c.pl
    @87
    @15
    @18
    @16
    @62
    cR
    @1
    cM
    @14
    @33
    lincsum.p
    @62
    eqid
    @51
    @84
    cS
    @62
    cplusg
    lincsum.s
    fveq2i
    lmodvsdir
    syl13anc
    eqtrd
    mpteq2dva
    oveq2d
    3adant3
    eqtrd
    @13
    @31
    cA
    cV
    @29
    co
    #
    cB
    cV
    @29
    co
    #
    c.pl
    co
    #
    @27
    cX
    @93
    cY
    @94
    c.pl
    lincsum.x
    lincsum.y
    oveq12i
    @4
    @8
    @95
    @27
    wceq
    @12
    @70
    @93
    @24
    @94
    @26
    c.pl
    @70
    @0
    cA
    @64
    wcel
    #
    @3
    @93
    @24
    wceq
    @92
    @6
    @96
    @4
    @7
    @6
    @96
    @5
    @64
    cA
    cR
    @63
    cV
    cmap
    @84
    oveq1i
    #
    eleq2i
    biimpi
    ad2antrl
    @71
    vx
    cA
    cM
    cV
    clmod
    lincval
    syl3anc
    @70
    @0
    cB
    @64
    wcel
    #
    @3
    @94
    @26
    wceq
    @92
    @7
    @98
    @4
    @6
    @7
    @98
    @5
    @64
    cB
    @97
    eleq2i
    biimpi
    ad2antll
    @71
    vx
    cB
    cM
    cV
    clmod
    lincval
    syl3anc
    oveq12d
    3adant3
    syl5eq
    3eqtr4rd
end
