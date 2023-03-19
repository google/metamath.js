include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "csg.mm"
include "eqid.mm"
include "scmatscmid.mm"
include "3expa.mm"
include "adantrr.mm"
include "wi.mm"
include "3expia.mm"
include "oveq12.mm"
include "adantl.mm"
include "csca.mm"
include "cbs.mm"
include "clmod.mm"
include "matlmod.mm"
include "ad2antrr.mm"
include "matsca2.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "adantr.mm"
include "imp.mm"
include "biimpa.mm"
include "matring.mm"
include "ringidcl.mm"
include "syl.mm"
include "lmodsubdir.mm"
include "eqcomd.mm"
include "simpll.mm"
include "oveqd.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "simpr.mm"
include "simplr.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "matvscl.mm"
include "syl12anc.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "scmatel.mm"
include "mpbir2and.mm"
include "exp32.mm"
include "rexlimdva.mm"
include "com23.mm"
include "syldc.mm"
include "impcom.mm"
include "mpd.mm"

theorem scmatsubcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cE: class E
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vd: setvar d
  let ve: setvar e
  let vc: setvar c
  assume scmatid.a: |- A = ( N Mat R )
  assume scmatid.b: |- B = ( Base ` A )
  assume scmatid.e: |- E = ( Base ` R )
  assume scmatid.0: |- .0. = ( 0g ` R )
  assume scmatid.s: |- S = ( N ScMat R )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( X e. S /\ Y e. S ) ) -> ( X ( -g ` A ) Y ) e. S )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cX
    cS
    wcel
    #
    cY
    cS
    wcel
    #
    wa
    #
    wa
    cX
    vc
    cv
    #
    cA
    cur
    cfv
    #
    cA
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vc
    cE
    wrex
    #
    cX
    cY
    cA
    csg
    cfv
    #
    co
    #
    cS
    wcel
    #
    @2
    @3
    @11
    @4
    @0
    @1
    @3
    @11
    cA
    cB
    cR
    cS
    @8
    @7
    cE
    cX
    cN
    crg
    vc
    scmatid.e
    scmatid.a
    scmatid.b
    @7
    eqid
    #
    @8
    eqid
    #
    scmatid.s
    scmatscmid
    3expa
    adantrr
    @5
    @2
    @11
    @14
    wi
    #
    @4
    @2
    @17
    wi
    @3
    @2
    @4
    cY
    vd
    cv
    #
    @7
    @8
    co
    #
    wceq
    #
    vd
    cE
    wrex
    #
    @17
    @0
    @1
    @4
    @21
    cA
    cB
    cR
    cS
    @8
    @7
    cE
    cY
    cN
    crg
    vd
    scmatid.e
    scmatid.a
    scmatid.b
    @15
    @16
    scmatid.s
    scmatscmid
    3expia
    @2
    @20
    @17
    vd
    cE
    @2
    @18
    cE
    wcel
    #
    wa
    #
    @11
    @20
    @14
    @23
    @10
    @20
    @14
    wi
    vc
    cE
    @23
    @6
    cE
    wcel
    #
    wa
    #
    @10
    @20
    @14
    @25
    @10
    @20
    wa
    #
    wa
    @13
    @9
    @19
    @12
    co
    #
    cS
    @26
    @13
    @27
    wceq
    @25
    cX
    @9
    cY
    @19
    @12
    oveq12
    adantl
    @25
    @27
    cS
    wcel
    @26
    @25
    @27
    @6
    @18
    cA
    csca
    cfv
    #
    csg
    cfv
    #
    co
    #
    @7
    @8
    co
    #
    cS
    @25
    @31
    @27
    @25
    @6
    @18
    @29
    @8
    @28
    @28
    cbs
    cfv
    #
    @12
    cB
    cA
    @7
    scmatid.b
    @16
    @28
    eqid
    @32
    eqid
    @12
    eqid
    @29
    eqid
    @2
    cA
    clmod
    wcel
    @22
    @24
    cA
    cR
    cN
    scmatid.a
    matlmod
    ad2antrr
    @23
    @24
    @6
    @32
    wcel
    #
    @2
    @24
    @33
    wi
    @22
    @2
    @24
    @33
    @2
    cE
    @32
    @6
    @2
    cE
    cR
    cbs
    cfv
    @32
    scmatid.e
    @2
    cR
    @28
    cbs
    cA
    cR
    cN
    crg
    scmatid.a
    matsca2
    #
    fveq2d
    syl5eq
    #
    eleq2d
    biimpd
    adantr
    imp
    @23
    @18
    @32
    wcel
    #
    @24
    @2
    @22
    @36
    @2
    cE
    @32
    @18
    @35
    eleq2d
    biimpa
    adantr
    @2
    @7
    cB
    wcel
    #
    @22
    @24
    @2
    cA
    crg
    wcel
    @37
    cA
    cR
    cN
    scmatid.a
    matring
    cB
    cA
    @7
    scmatid.b
    @15
    ringidcl
    syl
    ad2antrr
    #
    lmodsubdir
    eqcomd
    @25
    @31
    cS
    wcel
    #
    @31
    cB
    wcel
    #
    @31
    ve
    cv
    #
    @7
    @8
    co
    #
    wceq
    #
    ve
    cE
    wrex
    #
    @25
    @2
    @30
    cE
    wcel
    @37
    @40
    @2
    @22
    @24
    simpll
    @25
    @30
    @6
    @18
    cR
    csg
    cfv
    #
    co
    #
    cE
    @25
    @29
    @45
    @6
    @18
    @25
    @28
    cR
    csg
    @2
    @28
    cR
    wceq
    @22
    @24
    @2
    cR
    @28
    @34
    eqcomd
    ad2antrr
    fveq2d
    oveqd
    @25
    cR
    cgrp
    wcel
    #
    @24
    @22
    @46
    cE
    wcel
    @2
    @47
    @22
    @24
    @1
    @47
    @0
    cR
    ringgrp
    adantl
    ad2antrr
    @23
    @24
    simpr
    @2
    @22
    @24
    simplr
    cE
    cR
    @45
    @6
    @18
    scmatid.e
    @45
    eqid
    grpsubcl
    syl3anc
    eqeltrd
    #
    @38
    cA
    cB
    @30
    cR
    @8
    cE
    cN
    @7
    scmatid.e
    scmatid.a
    scmatid.b
    @16
    matvscl
    syl12anc
    @25
    @43
    @31
    @31
    wceq
    #
    ve
    @30
    cE
    @48
    @41
    @30
    wceq
    #
    @43
    @49
    wb
    @25
    @50
    @42
    @31
    @31
    @41
    @30
    @7
    @8
    oveq1
    eqeq2d
    adantl
    @25
    @31
    eqidd
    rspcedvd
    @2
    @39
    @40
    @44
    wa
    wb
    @22
    @24
    cA
    cB
    cR
    cS
    @8
    @7
    cE
    @31
    cN
    crg
    ve
    scmatid.e
    scmatid.a
    scmatid.b
    @15
    @16
    scmatid.s
    scmatel
    ad2antrr
    mpbir2and
    eqeltrd
    adantr
    eqeltrd
    exp32
    rexlimdva
    com23
    rexlimdva
    syldc
    adantl
    impcom
    mpd
end
