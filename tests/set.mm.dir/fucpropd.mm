include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cfunc.mm"
include "co.mm"
include "cop.mm"
include "chom.mm"
include "cnat.mm"
include "cco.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "csb.mm"
include "ctp.mm"
include "cfuc.mm"
include "ccat.mm"
include "funcpropd.mm"
include "opeq2d.mm"
include "natpropd.mm"
include "sqxpeqd.mm"
include "wceq.mm"
include "wcel.mm"
include "adantr.mm"
include "wa.mm"
include "cvv.mm"
include "nfv.mm"
include "wnfc.mm"
include "nfcsb1v.mm"
include "a1i.mm"
include "fvexd.mm"
include "ad3antrrr.mm"
include "oveqd.mm"
include "oveqdr.mm"
include "homfeqbas.mm"
include "ad4antr.mm"
include "eqid.mm"
include "chomf.mm"
include "ad5antr.mm"
include "ccomf.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "simpllr.mm"
include "simp-4r.mm"
include "simpld.mm"
include "xp1st.mm"
include "syl.mm"
include "eqeltrd.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "ffvelrnda.mm"
include "simplr.mm"
include "xp2nd.mm"
include "simprd.mm"
include "simplrr.mm"
include "nat1st2nd.mm"
include "simpr.mm"
include "natcl.mm"
include "simplrl.mm"
include "comfeqval.mm"
include "mpteq12dva.mm"
include "mpt2eq123dva.mm"
include "csbeq1a.mm"
include "adantl.mm"
include "eqtrd.mm"
include "csbiedf.mm"
include "tpeq123d.mm"
include "eqidd.mm"
include "fucval.mm"
include "3eqtr4d.mm"

theorem fucpropd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fucpropd.1: |- ( ph -> ( Homf ` A ) = ( Homf ` B ) )
  assume fucpropd.2: |- ( ph -> ( comf ` A ) = ( comf ` B ) )
  assume fucpropd.3: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )
  assume fucpropd.4: |- ( ph -> ( comf ` C ) = ( comf ` D ) )
  assume fucpropd.a: |- ( ph -> A e. Cat )
  assume fucpropd.b: |- ( ph -> B e. Cat )
  assume fucpropd.c: |- ( ph -> C e. Cat )
  assume fucpropd.d: |- ( ph -> D e. Cat )


  assert |- ( ph -> ( A FuncCat C ) = ( B FuncCat D ) )

  proof
    wph
    cnx
    cbs
    cfv
    #
    cA
    cC
    cfunc
    co
    #
    cop
    #
    cnx
    chom
    cfv
    #
    cA
    cC
    cnat
    co
    #
    cop
    #
    cnx
    cco
    cfv
    #
    vv
    vh
    @1
    @1
    cxp
    #
    @1
    vf
    vv
    cv
    #
    c1st
    cfv
    #
    vg
    @8
    c2nd
    cfv
    #
    vb
    va
    vg
    cv
    #
    vh
    cv
    #
    @4
    co
    #
    vf
    cv
    #
    @11
    @4
    co
    #
    vx
    cA
    cbs
    cfv
    #
    vx
    cv
    #
    vb
    cv
    #
    cfv
    #
    @17
    va
    cv
    #
    cfv
    #
    @17
    @14
    c1st
    cfv
    #
    cfv
    #
    @17
    @11
    c1st
    cfv
    #
    cfv
    #
    cop
    #
    @17
    @12
    c1st
    cfv
    #
    cfv
    #
    cC
    cco
    cfv
    #
    co
    co
    #
    cmpt
    #
    cmpt2
    #
    csb
    #
    csb
    #
    cmpt2
    #
    cop
    #
    ctp
    @0
    cB
    cD
    cfunc
    co
    #
    cop
    #
    @3
    cB
    cD
    cnat
    co
    #
    cop
    #
    @6
    vv
    vh
    @37
    @37
    cxp
    #
    @37
    vf
    @9
    vg
    @10
    vb
    va
    @11
    @12
    @39
    co
    #
    @14
    @11
    @39
    co
    #
    vx
    cB
    cbs
    cfv
    #
    @19
    @21
    @26
    @28
    cD
    cco
    cfv
    #
    co
    co
    #
    cmpt
    #
    cmpt2
    #
    csb
    #
    csb
    #
    cmpt2
    #
    cop
    #
    ctp
    cA
    cC
    cfuc
    co
    #
    cB
    cD
    cfuc
    co
    #
    wph
    @2
    @38
    @5
    @40
    @36
    @52
    wph
    @1
    @37
    @0
    wph
    cA
    cB
    cC
    cD
    ccat
    fucpropd.1
    fucpropd.2
    fucpropd.3
    fucpropd.4
    fucpropd.a
    fucpropd.b
    fucpropd.c
    fucpropd.d
    funcpropd
    #
    opeq2d
    wph
    @4
    @39
    @3
    wph
    cA
    cB
    cC
    cD
    fucpropd.1
    fucpropd.2
    fucpropd.3
    fucpropd.4
    fucpropd.a
    fucpropd.b
    fucpropd.c
    fucpropd.d
    natpropd
    #
    opeq2d
    wph
    @35
    @51
    @6
    wph
    vv
    vh
    @7
    @1
    @34
    @41
    @37
    @50
    wph
    @1
    @37
    @55
    sqxpeqd
    wph
    @1
    @37
    wceq
    @8
    @7
    wcel
    #
    @55
    adantr
    wph
    @57
    @12
    @1
    wcel
    #
    wa
    #
    wa
    #
    vf
    @9
    @33
    @50
    cvv
    @60
    vf
    nfv
    vf
    @50
    wnfc
    @60
    vf
    @9
    @49
    nfcsb1v
    a1i
    @60
    @8
    c1st
    fvexd
    @60
    @14
    @9
    wceq
    #
    wa
    #
    @33
    @49
    @50
    @62
    vg
    @10
    @32
    @49
    cvv
    @62
    vg
    nfv
    vg
    @49
    wnfc
    @62
    vg
    @10
    @48
    nfcsb1v
    a1i
    @62
    @8
    c2nd
    fvexd
    @62
    @11
    @10
    wceq
    #
    wa
    #
    @32
    @48
    @49
    @64
    vb
    va
    @13
    @15
    @31
    @42
    @43
    @47
    @64
    @4
    @39
    @11
    @12
    wph
    @4
    @39
    wceq
    @59
    @61
    @63
    @56
    ad3antrrr
    #
    oveqd
    @64
    @18
    @13
    wcel
    #
    vf
    vg
    @4
    @39
    @65
    oveqdr
    @64
    @66
    @20
    @15
    wcel
    #
    wa
    #
    wa
    #
    vx
    @16
    @30
    @44
    @46
    wph
    @16
    @44
    wceq
    @59
    @61
    @63
    @68
    wph
    cA
    cB
    fucpropd.1
    homfeqbas
    ad4antr
    @69
    @17
    @16
    wcel
    #
    wa
    #
    cC
    cbs
    cfv
    #
    cC
    cD
    @45
    @29
    @21
    @19
    cC
    chom
    cfv
    #
    @23
    @25
    @28
    @72
    eqid
    #
    @73
    eqid
    #
    @29
    eqid
    #
    @45
    eqid
    #
    wph
    cC
    chomf
    cfv
    cD
    chomf
    cfv
    wceq
    @59
    @61
    @63
    @68
    @70
    fucpropd.3
    ad5antr
    wph
    cC
    ccomf
    cfv
    cD
    ccomf
    cfv
    wceq
    @59
    @61
    @63
    @68
    @70
    fucpropd.4
    ad5antr
    @69
    @16
    @72
    @17
    @22
    @69
    @16
    @72
    cA
    cC
    @22
    @14
    c2nd
    cfv
    #
    @16
    eqid
    #
    @74
    @69
    @1
    wrel
    #
    @14
    @1
    wcel
    @22
    @78
    @1
    wbr
    cA
    cC
    relfunc
    #
    @69
    @14
    @9
    @1
    @60
    @61
    @63
    @68
    simpllr
    @69
    @57
    @9
    @1
    wcel
    @69
    @57
    @58
    wph
    @59
    @61
    @63
    @68
    simp-4r
    #
    simpld
    #
    @8
    @1
    @1
    xp1st
    syl
    eqeltrd
    @14
    @1
    1st2ndbr
    sylancr
    funcf1
    ffvelrnda
    @69
    @16
    @72
    @17
    @24
    @69
    @16
    @72
    cA
    cC
    @24
    @11
    c2nd
    cfv
    #
    @79
    @74
    @69
    @80
    @11
    @1
    wcel
    @24
    @84
    @1
    wbr
    @81
    @69
    @11
    @10
    @1
    @62
    @63
    @68
    simplr
    @69
    @57
    @10
    @1
    wcel
    @83
    @8
    @1
    @1
    xp2nd
    syl
    eqeltrd
    @11
    @1
    1st2ndbr
    sylancr
    funcf1
    ffvelrnda
    @69
    @16
    @72
    @17
    @27
    @69
    @16
    @72
    cA
    cC
    @27
    @12
    c2nd
    cfv
    #
    @79
    @74
    @69
    @80
    @58
    @27
    @85
    @1
    wbr
    @81
    @69
    @57
    @58
    @82
    simprd
    @12
    @1
    1st2ndbr
    sylancr
    funcf1
    ffvelrnda
    @71
    @20
    @16
    cA
    cC
    @22
    @78
    @73
    @24
    @84
    @4
    @17
    @4
    eqid
    #
    @71
    @20
    cA
    cC
    @14
    @11
    @4
    @86
    @64
    @66
    @67
    @70
    simplrr
    nat1st2nd
    @79
    @75
    @69
    @70
    simpr
    #
    natcl
    @71
    @18
    @16
    cA
    cC
    @24
    @84
    @73
    @27
    @85
    @4
    @17
    @86
    @71
    @18
    cA
    cC
    @11
    @12
    @4
    @86
    @64
    @66
    @67
    @70
    simplrl
    nat1st2nd
    @79
    @75
    @87
    natcl
    comfeqval
    mpteq12dva
    mpt2eq123dva
    @63
    @48
    @49
    wceq
    @62
    vg
    @10
    @48
    csbeq1a
    adantl
    eqtrd
    csbiedf
    @61
    @49
    @50
    wceq
    @60
    vf
    @9
    @49
    csbeq1a
    adantl
    eqtrd
    csbiedf
    mpt2eq123dva
    opeq2d
    tpeq123d
    wph
    vx
    vv
    @16
    @1
    cA
    cC
    @53
    @35
    @29
    vf
    vg
    vh
    @4
    va
    vb
    @53
    eqid
    @1
    eqid
    @86
    @79
    @76
    fucpropd.a
    fucpropd.c
    wph
    @35
    eqidd
    fucval
    wph
    vx
    vv
    @44
    @37
    cB
    cD
    @54
    @51
    @45
    vf
    vg
    vh
    @39
    va
    vb
    @54
    eqid
    @37
    eqid
    @39
    eqid
    @44
    eqid
    @77
    fucpropd.b
    fucpropd.d
    wph
    @51
    eqidd
    fucval
    3eqtr4d
end
