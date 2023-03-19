include "csubmgm.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "cmgmhm.mm"
include "co.mm"
include "cmgm.mm"
include "cbs.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "mgmhmrcl.mm"
include "simpld.mm"
include "adantl.mm"
include "submgmmgm.mm"
include "ad2antrr.mm"
include "jca.mm"
include "wfn.mm"
include "eqid.mm"
include "mgmhmf.mm"
include "ffn.mm"
include "syl.mm"
include "simplr.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "submgmbas.mm"
include "feq3d.mm"
include "mpbid.mm"
include "mgmhmlin.mm"
include "3expb.mm"
include "adantll.mm"
include "ressplusg.mm"
include "ad3antrrr.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "ralrimivva.mm"
include "ismgmhm.mm"
include "resmgmhm2.mm"
include "ancoms.mm"
include "adantlr.mm"
include "impbida.mm"

theorem resmgmhm2b
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume resmgmhm2.u: |- U = ( T |`s X )


  assert |- ( ( X e. ( SubMgm ` T ) /\ ran F C_ X ) -> ( F e. ( S MgmHom T ) <-> F e. ( S MgmHom U ) ) )

  proof
    cX
    cT
    csubmgm
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
    cmgmhm
    co
    wcel
    #
    cF
    cS
    cU
    cmgmhm
    co
    wcel
    #
    @3
    @4
    wa
    #
    cS
    cmgm
    wcel
    #
    cU
    cmgm
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
    wa
    @5
    @6
    @7
    @8
    @4
    @7
    @3
    @4
    @7
    cT
    cmgm
    wcel
    cS
    cT
    cF
    mgmhmrcl
    simpld
    adantl
    @1
    @8
    @2
    @4
    cX
    cU
    cT
    resmgmhm2.u
    submgmmgm
    ad2antrr
    jca
    @6
    @11
    @21
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
    @22
    @6
    @9
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @23
    @4
    @25
    @3
    @9
    @24
    cS
    cT
    cF
    @9
    eqid
    #
    @24
    eqid
    mgmhmf
    adantl
    @9
    @24
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
    resmgmhm2.u
    submgmbas
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
    @29
    @15
    @32
    wceq
    #
    @3
    @4
    @27
    @28
    @33
    @9
    @14
    @31
    cS
    cT
    cF
    @12
    @13
    @26
    @14
    eqid
    #
    @31
    eqid
    #
    mgmhmlin
    3expb
    adantll
    @30
    @31
    @18
    @16
    @17
    @1
    @31
    @18
    wceq
    @2
    @4
    @29
    cX
    @31
    cT
    cU
    @0
    resmgmhm2.u
    @35
    ressplusg
    ad3antrrr
    oveqd
    eqtrd
    ralrimivva
    jca
    vx
    vy
    @9
    @10
    @14
    @18
    cS
    cU
    cF
    @26
    @10
    eqid
    @34
    @18
    eqid
    ismgmhm
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
    resmgmhm2.u
    resmgmhm2
    ancoms
    adantlr
    impbida
end
