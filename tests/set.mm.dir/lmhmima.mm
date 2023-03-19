include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cima.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "wral.mm"
include "csca.mm"
include "cbs.mm"
include "cghm.mm"
include "lmghm.mm"
include "adantr.mm"
include "clmod.mm"
include "lmhmlmod1.mm"
include "simpr.mm"
include "lsssubg.mm"
include "syl2anc.mm"
include "ghmima.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "wfn.mm"
include "wss.mm"
include "wf.mm"
include "eqid.mm"
include "lmhmf.mm"
include "ffn.mm"
include "syl.mm"
include "lssss.mm"
include "fvelimab.mm"
include "simpll.mm"
include "lmhmsca.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "adantrr.mm"
include "sselda.mm"
include "adantrl.mm"
include "lmhmlin.mm"
include "syl3anc.mm"
include "3syl.mm"
include "simplr.mm"
include "simprr.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "fnfvima.mm"
include "eqeltrrd.mm"
include "anassrs.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "impr.mm"
include "ralrimivva.mm"
include "lmhmlmod2.mm"
include "islss4.mm"
include "mpbir2and.mm"

theorem lmhmima
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume lmhmima.x: |- X = ( LSubSp ` S )
  assume lmhmima.y: |- Y = ( LSubSp ` T )


  assert |- ( ( F e. ( S LMHom T ) /\ U e. X ) -> ( F " U ) e. Y )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cU
    cX
    wcel
    #
    wa
    #
    cF
    cU
    cima
    #
    cY
    wcel
    #
    @3
    cT
    csubg
    cfv
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cT
    cvsca
    cfv
    #
    co
    #
    @3
    wcel
    #
    vb
    @3
    wral
    va
    cT
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    #
    @2
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cU
    cS
    csubg
    cfv
    wcel
    #
    @5
    @0
    @14
    @1
    cS
    cT
    cF
    lmghm
    adantr
    @2
    cS
    clmod
    wcel
    #
    @1
    @15
    @0
    @16
    @1
    cS
    cT
    cF
    lmhmlmod1
    adantr
    #
    @0
    @1
    simpr
    #
    cX
    cU
    cS
    lmhmima.x
    lsssubg
    syl2anc
    cS
    cT
    cU
    cF
    ghmima
    syl2anc
    @2
    @10
    va
    vb
    @12
    @3
    @2
    @6
    @12
    wcel
    #
    @7
    @3
    wcel
    #
    @10
    @2
    @19
    wa
    #
    @20
    vc
    cv
    #
    cF
    cfv
    #
    @7
    wceq
    #
    vc
    cU
    wrex
    #
    @10
    @2
    @20
    @25
    wb
    #
    @19
    @2
    cF
    cS
    cbs
    cfv
    #
    wfn
    #
    cU
    @27
    wss
    #
    @26
    @2
    @27
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @28
    @0
    @31
    @1
    @27
    @30
    cS
    cT
    cF
    @27
    eqid
    #
    @30
    eqid
    #
    lmhmf
    #
    adantr
    @27
    @30
    cF
    ffn
    #
    syl
    @2
    @1
    @29
    @18
    cX
    cU
    @27
    cS
    @32
    lmhmima.x
    lssss
    #
    syl
    #
    vc
    @27
    cU
    @7
    cF
    fvelimab
    syl2anc
    adantr
    @21
    @24
    @10
    vc
    cU
    @21
    @22
    cU
    wcel
    #
    wa
    @6
    @23
    @8
    co
    #
    @3
    wcel
    #
    @24
    @10
    @2
    @19
    @38
    @40
    @2
    @19
    @38
    wa
    #
    wa
    #
    @6
    @22
    cS
    cvsca
    cfv
    #
    co
    #
    cF
    cfv
    #
    @39
    @3
    @42
    @0
    @6
    cS
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @22
    @27
    wcel
    #
    @45
    @39
    wceq
    @0
    @1
    @41
    simpll
    #
    @2
    @19
    @48
    @38
    @2
    @19
    @48
    @2
    @12
    @47
    @6
    @2
    @11
    @46
    cbs
    @0
    @11
    @46
    wceq
    @1
    cS
    cT
    cF
    @46
    @11
    @46
    eqid
    #
    @11
    eqid
    #
    lmhmsca
    adantr
    fveq2d
    eleq2d
    biimpa
    adantrr
    #
    @2
    @38
    @49
    @19
    @2
    cU
    @27
    @22
    @37
    sselda
    adantrl
    @47
    cS
    cT
    @43
    @8
    @27
    cF
    @46
    @6
    @22
    @51
    @47
    eqid
    #
    @32
    @43
    eqid
    #
    @8
    eqid
    #
    lmhmlin
    syl3anc
    @42
    @28
    @29
    @44
    cU
    wcel
    #
    @45
    @3
    wcel
    @42
    @0
    @31
    @28
    @50
    @34
    @35
    3syl
    @42
    @1
    @29
    @0
    @1
    @41
    simplr
    #
    @36
    syl
    @42
    @16
    @1
    @48
    @38
    @57
    @2
    @16
    @41
    @17
    adantr
    @58
    @53
    @2
    @19
    @38
    simprr
    @47
    cX
    @43
    cU
    @46
    cS
    @6
    @22
    @51
    @55
    @54
    lmhmima.x
    lssvscl
    syl22anc
    @27
    cU
    cF
    @44
    fnfvima
    syl3anc
    eqeltrrd
    anassrs
    @24
    @39
    @9
    @3
    @23
    @7
    @6
    @8
    oveq2
    eleq1d
    syl5ibcom
    rexlimdva
    sylbid
    impr
    ralrimivva
    @2
    cT
    clmod
    wcel
    #
    @4
    @5
    @13
    wa
    wb
    @0
    @59
    @1
    cS
    cT
    cF
    lmhmlmod2
    adantr
    @12
    cY
    @8
    @3
    @11
    @30
    cT
    va
    vb
    @52
    @12
    eqid
    @33
    @56
    lmhmima.y
    islss4
    syl
    mpbir2and
end
