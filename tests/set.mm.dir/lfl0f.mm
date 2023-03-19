include "clmod.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "cmulr.mm"
include "wceq.mm"
include "wral.mm"
include "wss.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fconst.mm"
include "eqid.mm"
include "lmod0cl.mm"
include "snssd.mm"
include "fss.mm"
include "sylancr.mm"
include "wa.mm"
include "crg.mm"
include "lmodring.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "grpidcl.mm"
include "grplid.mm"
include "eqtrd.mm"
include "simplrr.mm"
include "fvconst2.mm"
include "oveq2d.mm"
include "adantl.mm"
include "oveq12d.mm"
include "simpll.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "simpr.mm"
include "lmodvacl.mm"
include "3eqtr4rd.mm"
include "ralrimiva.mm"
include "ralrimivva.mm"
include "islfl.mm"
include "mpbir2and.mm"

theorem lfl0f
  let cD: class D
  let cF: class F
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume lfl0f.d: |- D = ( Scalar ` W )
  assume lfl0f.o: |- .0. = ( 0g ` D )
  assume lfl0f.v: |- V = ( Base ` W )
  assume lfl0f.f: |- F = ( LFnl ` W )


  assert |- ( W e. LMod -> ( V X. { .0. } ) e. F )

  proof
    cW
    clmod
    wcel
    #
    cV
    c.0
    csn
    #
    cxp
    #
    cF
    wcel
    cV
    cD
    cbs
    cfv
    #
    @2
    wf
    #
    vr
    cv
    #
    vx
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    vy
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    @2
    cfv
    #
    @5
    @6
    @2
    cfv
    #
    cD
    cmulr
    cfv
    #
    co
    #
    @9
    @2
    cfv
    #
    cD
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    cV
    wral
    #
    vx
    cV
    wral
    vr
    @3
    wral
    @0
    cV
    @1
    @2
    wf
    @1
    @3
    wss
    @4
    cV
    c.0
    c.0
    cD
    c0g
    cfv
    cvv
    lfl0f.o
    cD
    c0g
    fvex
    eqeltri
    #
    fconst
    @0
    c.0
    @3
    cD
    @3
    cW
    c.0
    lfl0f.d
    @3
    eqid
    #
    lfl0f.o
    lmod0cl
    snssd
    cV
    @1
    @3
    @2
    fss
    sylancr
    @0
    @20
    vr
    vx
    @3
    cV
    @0
    @5
    @3
    wcel
    #
    @6
    cV
    wcel
    #
    wa
    #
    wa
    #
    @19
    vy
    cV
    @26
    @9
    cV
    wcel
    #
    wa
    #
    @5
    c.0
    @14
    co
    #
    c.0
    @17
    co
    #
    c.0
    @18
    @12
    @28
    @30
    c.0
    c.0
    @17
    co
    #
    c.0
    @28
    @29
    c.0
    c.0
    @17
    @28
    cD
    crg
    wcel
    #
    @23
    @29
    c.0
    wceq
    @0
    @32
    @25
    @27
    cD
    cW
    lfl0f.d
    lmodring
    ad2antrr
    #
    @0
    @23
    @24
    @27
    simplrl
    #
    @3
    cD
    @14
    @5
    c.0
    @22
    @14
    eqid
    #
    lfl0f.o
    ringrz
    syl2anc
    oveq1d
    @28
    cD
    cgrp
    wcel
    #
    c.0
    @3
    wcel
    #
    @31
    c.0
    wceq
    @28
    @32
    @36
    @33
    cD
    ringgrp
    syl
    #
    @28
    @36
    @37
    @38
    @3
    cD
    c.0
    @22
    lfl0f.o
    grpidcl
    syl
    @3
    @17
    cD
    c.0
    c.0
    @22
    @17
    eqid
    #
    lfl0f.o
    grplid
    syl2anc
    eqtrd
    @28
    @15
    @29
    @16
    c.0
    @17
    @28
    @13
    c.0
    @5
    @14
    @28
    @24
    @13
    c.0
    wceq
    @0
    @23
    @24
    @27
    simplrr
    #
    cV
    c.0
    @6
    @21
    fvconst2
    syl
    oveq2d
    @27
    @16
    c.0
    wceq
    @26
    cV
    c.0
    @9
    @21
    fvconst2
    adantl
    oveq12d
    @28
    @11
    cV
    wcel
    #
    @12
    c.0
    wceq
    @28
    @0
    @8
    cV
    wcel
    #
    @27
    @41
    @0
    @25
    @27
    simpll
    #
    @28
    @0
    @23
    @24
    @42
    @43
    @34
    @40
    @5
    @7
    cD
    @3
    cV
    cW
    @6
    lfl0f.v
    lfl0f.d
    @7
    eqid
    #
    @22
    lmodvscl
    syl3anc
    @26
    @27
    simpr
    @10
    cV
    cW
    @8
    @9
    lfl0f.v
    @10
    eqid
    #
    lmodvacl
    syl3anc
    cV
    c.0
    @11
    @21
    fvconst2
    syl
    3eqtr4rd
    ralrimiva
    ralrimivva
    vx
    vy
    cD
    @10
    @17
    @7
    @14
    cF
    @2
    @3
    cV
    cW
    clmod
    vr
    lfl0f.v
    @45
    lfl0f.d
    @44
    @22
    @39
    @35
    lfl0f.f
    islfl
    mpbir2and
end
