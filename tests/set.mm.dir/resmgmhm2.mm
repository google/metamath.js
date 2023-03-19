include "cmgmhm.mm"
include "co.mm"
include "wcel.mm"
include "csubmgm.mm"
include "cfv.mm"
include "wa.mm"
include "cmgm.mm"
include "cbs.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "mgmhmrcl.mm"
include "simpld.mm"
include "submgmrcl.mm"
include "anim12i.mm"
include "wss.mm"
include "eqid.mm"
include "mgmhmf.mm"
include "submgmbas.mm"
include "submgmss.mm"
include "eqsstr3d.mm"
include "fss.mm"
include "syl2an.mm"
include "mgmhmlin.mm"
include "3expb.mm"
include "adantlr.mm"
include "ressplusg.mm"
include "ad2antlr.mm"
include "oveqd.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "jca.mm"
include "ismgmhm.mm"
include "sylanbrc.mm"

theorem resmgmhm2
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume resmgmhm2.u: |- U = ( T |`s X )


  assert |- ( ( F e. ( S MgmHom U ) /\ X e. ( SubMgm ` T ) ) -> F e. ( S MgmHom T ) )

  proof
    cF
    cS
    cU
    cmgmhm
    co
    wcel
    #
    cX
    cT
    csubmgm
    cfv
    #
    wcel
    #
    wa
    #
    cS
    cmgm
    wcel
    #
    cT
    cmgm
    wcel
    #
    wa
    cS
    cbs
    cfv
    #
    cT
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
    @9
    cF
    cfv
    #
    @10
    cF
    cfv
    #
    cT
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    @6
    wral
    vx
    @6
    wral
    #
    wa
    cF
    cS
    cT
    cmgmhm
    co
    wcel
    @0
    @4
    @2
    @5
    @0
    @4
    cU
    cmgm
    wcel
    cS
    cU
    cF
    mgmhmrcl
    simpld
    cX
    cT
    submgmrcl
    anim12i
    @3
    @8
    @18
    @0
    @6
    cU
    cbs
    cfv
    #
    cF
    wf
    @19
    @7
    wss
    @8
    @2
    @6
    @19
    cS
    cU
    cF
    @6
    eqid
    #
    @19
    eqid
    mgmhmf
    @2
    @19
    cX
    @7
    cX
    cU
    cT
    resmgmhm2.u
    submgmbas
    @7
    cX
    cT
    @7
    eqid
    #
    submgmss
    eqsstr3d
    @6
    @19
    @7
    cF
    fss
    syl2an
    @3
    @17
    vx
    vy
    @6
    @6
    @3
    @9
    @6
    wcel
    #
    @10
    @6
    wcel
    #
    wa
    #
    wa
    #
    @12
    @13
    @14
    cU
    cplusg
    cfv
    #
    co
    #
    @16
    @0
    @24
    @12
    @27
    wceq
    #
    @2
    @0
    @22
    @23
    @28
    @6
    @11
    @26
    cS
    cU
    cF
    @9
    @10
    @20
    @11
    eqid
    #
    @26
    eqid
    mgmhmlin
    3expb
    adantlr
    @25
    @15
    @26
    @13
    @14
    @2
    @15
    @26
    wceq
    @0
    @24
    cX
    @15
    cT
    cU
    @1
    resmgmhm2.u
    @15
    eqid
    #
    ressplusg
    ad2antlr
    oveqd
    eqtr4d
    ralrimivva
    jca
    vx
    vy
    @6
    @7
    @11
    @15
    cS
    cT
    cF
    @20
    @21
    @29
    @30
    ismgmhm
    sylanbrc
end
