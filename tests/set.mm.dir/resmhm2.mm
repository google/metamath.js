include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wa.mm"
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
include "submrcl.mm"
include "anim12i.mm"
include "wss.mm"
include "eqid.mm"
include "mhmf.mm"
include "submbas.mm"
include "submss.mm"
include "eqsstr3d.mm"
include "fss.mm"
include "syl2an.mm"
include "mhmlin.mm"
include "3expb.mm"
include "adantlr.mm"
include "ressplusg.mm"
include "ad2antlr.mm"
include "oveqd.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "mhm0.mm"
include "adantr.mm"
include "subm0.mm"
include "adantl.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem resmhm2
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume resmhm2.u: |- U = ( T |`s X )


  assert |- ( ( F e. ( S MndHom U ) /\ X e. ( SubMnd ` T ) ) -> F e. ( S MndHom T ) )

  proof
    cF
    cS
    cU
    cmhm
    co
    wcel
    #
    cX
    cT
    csubmnd
    cfv
    #
    wcel
    #
    wa
    #
    cS
    cmnd
    wcel
    #
    cT
    cmnd
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
    cS
    c0g
    cfv
    #
    cF
    cfv
    #
    cT
    c0g
    cfv
    #
    wceq
    #
    w3a
    cF
    cS
    cT
    cmhm
    co
    wcel
    @0
    @4
    @2
    @5
    cS
    cU
    cF
    mhmrcl1
    cX
    cT
    submrcl
    anim12i
    @3
    @8
    @18
    @22
    @0
    @6
    cU
    cbs
    cfv
    #
    cF
    wf
    @23
    @7
    wss
    @8
    @2
    @6
    @23
    cS
    cU
    cF
    @6
    eqid
    #
    @23
    eqid
    mhmf
    @2
    @23
    cX
    @7
    cX
    cU
    cT
    resmhm2.u
    submbas
    @7
    cX
    cT
    @7
    eqid
    #
    submss
    eqsstr3d
    @6
    @23
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
    @28
    @12
    @31
    wceq
    #
    @2
    @0
    @26
    @27
    @32
    @6
    @11
    @30
    cS
    cU
    cF
    @9
    @10
    @24
    @11
    eqid
    #
    @30
    eqid
    mhmlin
    3expb
    adantlr
    @29
    @15
    @30
    @13
    @14
    @2
    @15
    @30
    wceq
    @0
    @28
    cX
    @15
    cT
    cU
    @1
    resmhm2.u
    @15
    eqid
    #
    ressplusg
    ad2antlr
    oveqd
    eqtr4d
    ralrimivva
    @3
    @20
    cU
    c0g
    cfv
    #
    @21
    @0
    @20
    @35
    wceq
    @2
    cS
    cU
    cF
    @35
    @19
    @19
    eqid
    #
    @35
    eqid
    mhm0
    adantr
    @2
    @21
    @35
    wceq
    @0
    cX
    cU
    cT
    @21
    resmhm2.u
    @21
    eqid
    #
    subm0
    adantl
    eqtr4d
    3jca
    vx
    vy
    @6
    @7
    @11
    @15
    cS
    cT
    cF
    @21
    @19
    @24
    @25
    @33
    @34
    @36
    @37
    ismhm
    sylanbrc
end
