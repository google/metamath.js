include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
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
include "lmhmlmod2.mm"
include "lsssubg.mm"
include "sylan.mm"
include "ghmpreima.mm"
include "syl2anc.mm"
include "lmhmlmod1.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "lmhmf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "adantrl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "simpll.mm"
include "lmhmlin.mm"
include "simplr.mm"
include "lmhmsca.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "adantrr.mm"
include "wfun.mm"
include "ffun.mm"
include "simprr.mm"
include "fvimacnvi.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "eqeltrd.mm"
include "wb.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "mpbir2and.mm"
include "ralrimivva.mm"
include "islss4.mm"

theorem lmhmpreima
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


  assert |- ( ( F e. ( S LMHom T ) /\ U e. Y ) -> ( `' F " U ) e. X )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cU
    cY
    wcel
    #
    wa
    #
    cF
    ccnv
    cU
    cima
    #
    cX
    wcel
    #
    @3
    cS
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
    cS
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
    cS
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
    cT
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
    @0
    cT
    clmod
    wcel
    #
    @1
    @15
    cS
    cT
    cF
    lmhmlmod2
    #
    cY
    cU
    cT
    lmhmima.y
    lsssubg
    sylan
    cS
    cT
    cF
    cU
    ghmpreima
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
    wa
    #
    wa
    #
    @10
    @9
    cS
    cbs
    cfv
    #
    wcel
    #
    @9
    cF
    cfv
    #
    cU
    wcel
    #
    @21
    cS
    clmod
    wcel
    #
    @18
    @7
    @22
    wcel
    #
    @23
    @0
    @26
    @1
    @20
    cS
    cT
    cF
    lmhmlmod1
    #
    ad2antrr
    @2
    @18
    @19
    simprl
    #
    @2
    @19
    @27
    @18
    @2
    @3
    @22
    @7
    @2
    cF
    cdm
    #
    @3
    @22
    cF
    cU
    cnvimass
    @2
    @22
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @30
    @22
    wceq
    @0
    @32
    @1
    @22
    @31
    cS
    cT
    cF
    @22
    eqid
    #
    @31
    eqid
    lmhmf
    adantr
    #
    @22
    @31
    cF
    fdm
    syl
    syl5sseq
    sselda
    adantrl
    #
    @6
    @8
    @11
    @12
    @22
    cS
    @7
    @33
    @11
    eqid
    #
    @8
    eqid
    #
    @12
    eqid
    #
    lmodvscl
    syl3anc
    @21
    @24
    @6
    @7
    cF
    cfv
    #
    cT
    cvsca
    cfv
    #
    co
    #
    cU
    @21
    @0
    @18
    @27
    @24
    @41
    wceq
    @0
    @1
    @20
    simpll
    @29
    @35
    @12
    cS
    cT
    @8
    @40
    @22
    cF
    @11
    @6
    @7
    @36
    @38
    @33
    @37
    @40
    eqid
    #
    lmhmlin
    syl3anc
    @21
    @16
    @1
    @6
    cT
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @39
    cU
    wcel
    #
    @41
    cU
    wcel
    @0
    @16
    @1
    @20
    @17
    ad2antrr
    @0
    @1
    @20
    simplr
    @2
    @18
    @45
    @19
    @2
    @45
    @18
    @2
    @44
    @12
    @6
    @2
    @43
    @11
    cbs
    @0
    @43
    @11
    wceq
    @1
    cS
    cT
    cF
    @11
    @43
    @36
    @43
    eqid
    #
    lmhmsca
    adantr
    fveq2d
    eleq2d
    biimpar
    adantrr
    @21
    cF
    wfun
    #
    @19
    @46
    @2
    @48
    @20
    @2
    @32
    @48
    @34
    @22
    @31
    cF
    ffun
    syl
    adantr
    @2
    @18
    @19
    simprr
    @7
    cU
    cF
    fvimacnvi
    syl2anc
    @44
    cY
    @40
    cU
    @43
    cT
    @6
    @39
    @47
    @42
    @44
    eqid
    lmhmima.y
    lssvscl
    syl22anc
    eqeltrd
    @2
    @10
    @23
    @25
    wa
    wb
    #
    @20
    @2
    @32
    cF
    @22
    wfn
    @49
    @34
    @22
    @31
    cF
    ffn
    @22
    @9
    cU
    cF
    elpreima
    3syl
    adantr
    mpbir2and
    ralrimivva
    @2
    @26
    @4
    @5
    @13
    wa
    wb
    @0
    @26
    @1
    @28
    adantr
    @12
    cX
    @8
    @3
    @11
    @22
    cS
    va
    vb
    @36
    @38
    @33
    @37
    lmhmima.x
    islss4
    syl
    mpbir2and
end
