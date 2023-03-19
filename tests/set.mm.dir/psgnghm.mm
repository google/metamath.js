include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "cmul.mm"
include "cdm.mm"
include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "cbs.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cfn.mm"
include "crab.mm"
include "wfn.mm"
include "eqid.mm"
include "psgnfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ressbas2.mm"
include "cnmsgnbas.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ressplusg.mm"
include "prex.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "csubg.mm"
include "cgrp.mm"
include "psgndmsubg.mm"
include "subggrp.mm"
include "syl.mm"
include "cnmsgngrp.mm"
include "a1i.mm"
include "wral.mm"
include "wf.mm"
include "wfun.mm"
include "fnfun.mm"
include "funfn.mm"
include "mpbi.mm"
include "cgsu.mm"
include "co.mm"
include "chash.mm"
include "cexp.mm"
include "wa.mm"
include "cpmtr.mm"
include "crn.mm"
include "cword.mm"
include "wrex.mm"
include "psgnvali.mm"
include "wi.mm"
include "cz.mm"
include "lencl.mm"
include "nn0zd.mm"
include "m1expcl2.mm"
include "prcom.mm"
include "syl6eleq.mm"
include "adantl.mm"
include "eleq1a.mm"
include "adantld.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "anim12i.mm"
include "reeanv.mm"
include "sylibr.mm"
include "cconcat.mm"
include "ccatcl.mm"
include "psgnvalii.mm"
include "sylan2.mm"
include "cmnd.mm"
include "symggrp.mm"
include "grpmnd.mm"
include "symgtrf.mm"
include "sswrd.mm"
include "sseli.mm"
include "gsumccat.mm"
include "syl3an.mm"
include "3expb.mm"
include "fveq2d.mm"
include "caddc.mm"
include "ccatlen.mm"
include "oveq2d.mm"
include "cc.mm"
include "neg1cn.mm"
include "cn0.mm"
include "ad2antll.mm"
include "ad2antrl.mm"
include "expaddd.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "oveq12.mm"
include "eqeqan12d.mm"
include "an4s.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "imp.mm"
include "isghmd.mm"

theorem psgnghm
  let cD: class D
  let cS: class S
  let cU: class U
  let cF: class F
  let cN: class N
  let cV: class V
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume psgnghm.s: |- S = ( SymGrp ` D )
  assume psgnghm.n: |- N = ( pmSgn ` D )
  assume psgnghm.f: |- F = ( S |`s dom N )
  assume psgnghm.u: |- U = ( ( mulGrp ` CCfld ) |`s { 1 , -u 1 } )


  assert |- ( D e. V -> N e. ( F GrpHom U ) )

  proof
    cD
    cV
    wcel
    #
    vx
    vy
    cS
    cplusg
    cfv
    #
    cmul
    cF
    cU
    cN
    cN
    cdm
    #
    c1
    c1
    cneg
    #
    cpr
    #
    @2
    cS
    cbs
    cfv
    #
    wss
    @2
    cF
    cbs
    cfv
    #
    wceq
    @2
    vx
    cv
    #
    cid
    cdif
    cdm
    cfn
    wcel
    #
    vx
    @5
    crab
    #
    @5
    cN
    @9
    wfn
    #
    @2
    @9
    wceq
    @5
    cD
    @9
    cS
    cN
    vx
    psgnghm.s
    @5
    eqid
    #
    @9
    eqid
    psgnghm.n
    psgnfn
    #
    @9
    cN
    fndm
    ax-mp
    @8
    vx
    @5
    ssrab2
    eqsstri
    @2
    @5
    cF
    cS
    psgnghm.f
    @11
    ressbas2
    ax-mp
    #
    cU
    psgnghm.u
    cnmsgnbas
    @2
    cvv
    wcel
    @1
    cF
    cplusg
    cfv
    wceq
    @2
    @6
    cvv
    @13
    cF
    cbs
    fvex
    eqeltri
    @2
    @1
    cS
    cF
    cvv
    psgnghm.f
    @1
    eqid
    #
    ressplusg
    ax-mp
    @4
    cvv
    wcel
    cmul
    cU
    cplusg
    cfv
    wceq
    c1
    @3
    prex
    @4
    cmul
    ccnfld
    cmgp
    cfv
    #
    cU
    cvv
    psgnghm.u
    ccnfld
    cmul
    @15
    @15
    eqid
    cnfldmul
    mgpplusg
    ressplusg
    ax-mp
    @0
    @2
    cS
    csubg
    cfv
    wcel
    cF
    cgrp
    wcel
    cD
    cS
    cN
    cV
    psgnghm.s
    psgnghm.n
    psgndmsubg
    @2
    cS
    cF
    psgnghm.f
    subggrp
    syl
    cU
    cgrp
    wcel
    @0
    cU
    psgnghm.u
    cnmsgngrp
    a1i
    @0
    cN
    @2
    wfn
    #
    @7
    cN
    cfv
    #
    @4
    wcel
    #
    vx
    @2
    wral
    @2
    @4
    cN
    wf
    @16
    @0
    cN
    wfun
    #
    @16
    @10
    @19
    @12
    @9
    cN
    fnfun
    ax-mp
    cN
    funfn
    mpbi
    a1i
    @0
    @18
    vx
    @2
    @7
    @2
    wcel
    #
    @7
    cS
    vz
    cv
    #
    cgsu
    co
    #
    wceq
    #
    @17
    @3
    @21
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    wa
    #
    vz
    cD
    cpmtr
    cfv
    crn
    #
    cword
    #
    wrex
    #
    @0
    @18
    vz
    cD
    @7
    @28
    cS
    cN
    psgnghm.s
    @28
    eqid
    #
    psgnghm.n
    psgnvali
    #
    @0
    @27
    @18
    vz
    @29
    @0
    @21
    @29
    wcel
    #
    wa
    #
    @26
    @18
    @23
    @34
    @25
    @4
    wcel
    #
    @26
    @18
    wi
    @33
    @35
    @0
    @33
    @24
    cz
    wcel
    #
    @35
    @33
    @24
    @28
    @21
    lencl
    #
    nn0zd
    @36
    @25
    @3
    c1
    cpr
    @4
    @24
    m1expcl2
    @3
    c1
    prcom
    syl6eleq
    syl
    adantl
    @25
    @4
    @17
    eleq1a
    syl
    adantld
    rexlimdva
    syl5
    ralrimiv
    vx
    @2
    @4
    cN
    ffnfv
    sylanbrc
    @0
    @20
    vy
    cv
    #
    @2
    wcel
    #
    wa
    #
    @7
    @38
    @1
    co
    #
    cN
    cfv
    #
    @17
    @38
    cN
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @40
    @27
    @38
    cS
    vw
    cv
    #
    cgsu
    co
    #
    wceq
    #
    @43
    @3
    @46
    chash
    cfv
    #
    cexp
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    vw
    @29
    wrex
    vz
    @29
    wrex
    #
    @0
    @45
    @40
    @30
    @52
    vw
    @29
    wrex
    #
    wa
    @54
    @20
    @30
    @39
    @55
    @32
    vw
    cD
    @38
    @28
    cS
    cN
    psgnghm.s
    @31
    psgnghm.n
    psgnvali
    anim12i
    @27
    @52
    vz
    vw
    @29
    @29
    reeanv
    sylibr
    @0
    @53
    @45
    vz
    vw
    @29
    @29
    @0
    @33
    @46
    @29
    wcel
    #
    wa
    #
    wa
    #
    @45
    @53
    @22
    @47
    @1
    co
    #
    cN
    cfv
    #
    @25
    @50
    cmul
    co
    #
    wceq
    #
    @58
    cS
    @21
    @46
    cconcat
    co
    #
    cgsu
    co
    #
    cN
    cfv
    #
    @3
    @63
    chash
    cfv
    #
    cexp
    co
    #
    @60
    @61
    @57
    @0
    @63
    @29
    wcel
    @65
    @67
    wceq
    @28
    @21
    @46
    ccatcl
    cD
    @28
    cS
    cN
    cV
    @63
    psgnghm.s
    @31
    psgnghm.n
    psgnvalii
    sylan2
    @58
    @64
    @59
    cN
    @0
    @33
    @56
    @64
    @59
    wceq
    #
    @0
    cS
    cmnd
    wcel
    #
    @33
    @21
    @5
    cword
    #
    wcel
    @56
    @46
    @70
    wcel
    @68
    @0
    cS
    cgrp
    wcel
    @69
    cD
    cS
    cV
    psgnghm.s
    symggrp
    cS
    grpmnd
    syl
    @29
    @70
    @21
    @28
    @5
    wss
    @29
    @70
    wss
    @5
    cD
    @28
    cS
    @31
    psgnghm.s
    @11
    symgtrf
    @28
    @5
    sswrd
    ax-mp
    #
    sseli
    @29
    @70
    @46
    @71
    sseli
    @5
    @1
    cS
    @21
    @46
    @11
    @14
    gsumccat
    syl3an
    3expb
    fveq2d
    @58
    @67
    @3
    @24
    @49
    caddc
    co
    #
    cexp
    co
    @61
    @58
    @66
    @72
    @3
    cexp
    @57
    @66
    @72
    wceq
    @0
    @28
    @21
    @46
    ccatlen
    adantl
    oveq2d
    @58
    @3
    @24
    @49
    @3
    cc
    wcel
    @58
    neg1cn
    a1i
    @56
    @49
    cn0
    wcel
    @0
    @33
    @28
    @46
    lencl
    ad2antll
    @33
    @24
    cn0
    wcel
    @0
    @56
    @37
    ad2antrl
    expaddd
    eqtrd
    3eqtr3d
    @23
    @48
    @26
    @51
    @45
    @62
    wb
    @23
    @48
    wa
    #
    @26
    @51
    wa
    @42
    @60
    @44
    @61
    @73
    @41
    @59
    cN
    @7
    @22
    @38
    @47
    @1
    oveq12
    fveq2d
    @17
    @25
    @43
    @50
    cmul
    oveq12
    eqeqan12d
    an4s
    syl5ibrcom
    rexlimdvva
    syl5
    imp
    isghmd
end
