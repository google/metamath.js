include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "cmhm.mm"
include "co.mm"
include "cmnd.mm"
include "cbs.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "mhmrcl1.mm"
include "adantl.mm"
include "submmnd.mm"
include "ad2antrr.mm"
include "jca.mm"
include "wfn.mm"
include "eqid.mm"
include "mhmf.mm"
include "ffn.mm"
include "syl.mm"
include "simplr.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "submbas.mm"
include "feq3d.mm"
include "mpbid.mm"
include "mhmlin.mm"
include "3expb.mm"
include "adantll.mm"
include "ressplusg.mm"
include "ad3antrrr.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "ralrimivva.mm"
include "mhm0.mm"
include "subm0.mm"
include "3jca.mm"
include "ismhm.mm"
include "resmhm2.mm"
include "ancoms.mm"
include "adantlr.mm"
include "impbida.mm"

theorem resmhm2b
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume resmhm2.u: |- U = ( T |`s X )


  assert |- ( ( X e. ( SubMnd ` T ) /\ ran F C_ X ) -> ( F e. ( S MndHom T ) <-> F e. ( S MndHom U ) ) )

  proof
    cX
    cT
    csubmnd
    cfv
    #
    wcel
    #
    cF
    crn
    cX
    wss
    #
    wa
    #
    cF
    cS
    cT
    cmhm
    co
    wcel
    #
    cF
    cS
    cU
    cmhm
    co
    wcel
    #
    @3
    @4
    wa
    #
    cS
    cmnd
    wcel
    #
    cU
    cmnd
    wcel
    #
    wa
    cS
    cbs
    cfv
    #
    cU
    cbs
    cfv
    #
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    cF
    cfv
    #
    @12
    cF
    cfv
    #
    @13
    cF
    cfv
    #
    cU
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    @9
    wral
    vx
    @9
    wral
    #
    cS
    c0g
    cfv
    #
    cF
    cfv
    #
    cU
    c0g
    cfv
    #
    wceq
    #
    w3a
    @5
    @6
    @7
    @8
    @4
    @7
    @3
    cS
    cT
    cF
    mhmrcl1
    adantl
    @1
    @8
    @2
    @4
    cX
    cU
    cT
    resmhm2.u
    submmnd
    ad2antrr
    jca
    @6
    @11
    @21
    @25
    @6
    @9
    cX
    cF
    wf
    #
    @11
    @6
    cF
    @9
    wfn
    #
    @2
    @26
    @6
    @9
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @27
    @4
    @29
    @3
    @9
    @28
    cS
    cT
    cF
    @9
    eqid
    #
    @28
    eqid
    mhmf
    adantl
    @9
    @28
    cF
    ffn
    syl
    @1
    @2
    @4
    simplr
    @9
    cX
    cF
    df-f
    sylanbrc
    @6
    cX
    @10
    cF
    @9
    @1
    cX
    @10
    wceq
    @2
    @4
    cX
    cU
    cT
    resmhm2.u
    submbas
    ad2antrr
    feq3d
    mpbid
    @6
    @20
    vx
    vy
    @9
    @9
    @6
    @12
    @9
    wcel
    #
    @13
    @9
    wcel
    #
    wa
    #
    wa
    #
    @15
    @16
    @17
    cT
    cplusg
    cfv
    #
    co
    #
    @19
    @4
    @33
    @15
    @36
    wceq
    #
    @3
    @4
    @31
    @32
    @37
    @9
    @14
    @35
    cS
    cT
    cF
    @12
    @13
    @30
    @14
    eqid
    #
    @35
    eqid
    #
    mhmlin
    3expb
    adantll
    @34
    @35
    @18
    @16
    @17
    @1
    @35
    @18
    wceq
    @2
    @4
    @33
    cX
    @35
    cT
    cU
    @0
    resmhm2.u
    @39
    ressplusg
    ad3antrrr
    oveqd
    eqtrd
    ralrimivva
    @6
    @23
    cT
    c0g
    cfv
    #
    @24
    @4
    @23
    @40
    wceq
    @3
    cS
    cT
    cF
    @40
    @22
    @22
    eqid
    #
    @40
    eqid
    #
    mhm0
    adantl
    @1
    @40
    @24
    wceq
    @2
    @4
    cX
    cU
    cT
    @40
    resmhm2.u
    @42
    subm0
    ad2antrr
    eqtrd
    3jca
    vx
    vy
    @9
    @10
    @14
    @18
    cS
    cU
    cF
    @24
    @22
    @30
    @10
    eqid
    @38
    @18
    eqid
    @41
    @24
    eqid
    ismhm
    sylanbrc
    @1
    @5
    @4
    @2
    @5
    @1
    @4
    cS
    cT
    cU
    cF
    cX
    resmhm2.u
    resmhm2
    ancoms
    adantlr
    impbida
end
