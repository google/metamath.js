include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wa.mm"
include "cmnd.mm"
include "cbs.mm"
include "cres.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "mhmrcl2.mm"
include "submmnd.mm"
include "anim12ci.mm"
include "wss.mm"
include "eqid.mm"
include "mhmf.mm"
include "submss.mm"
include "fssres.mm"
include "syl2an.mm"
include "adantl.mm"
include "ressbas2.mm"
include "syl.mm"
include "feq2d.mm"
include "mpbid.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "mhmlin.mm"
include "syl3anc.mm"
include "submcl.mm"
include "3expb.mm"
include "adantll.mm"
include "fvres.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "subm0cl.mm"
include "subm0.mm"
include "mhm0.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem resmhm
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume resmhm.u: |- U = ( S |`s X )


  assert |- ( ( F e. ( S MndHom T ) /\ X e. ( SubMnd ` S ) ) -> ( F |` X ) e. ( U MndHom T ) )

  proof
    cF
    cS
    cT
    cmhm
    co
    wcel
    #
    cX
    cS
    csubmnd
    cfv
    #
    wcel
    #
    wa
    #
    cU
    cmnd
    wcel
    #
    cT
    cmnd
    wcel
    #
    wa
    cU
    cbs
    cfv
    #
    cT
    cbs
    cfv
    #
    cF
    cX
    cres
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cU
    cplusg
    cfv
    #
    co
    #
    @8
    cfv
    #
    @10
    @8
    cfv
    #
    @11
    @8
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
    #
    vx
    @6
    wral
    #
    cU
    c0g
    cfv
    #
    @8
    cfv
    #
    cT
    c0g
    cfv
    #
    wceq
    #
    w3a
    @8
    cU
    cT
    cmhm
    co
    wcel
    @0
    @5
    @2
    @4
    cS
    cT
    cF
    mhmrcl2
    cX
    cU
    cS
    resmhm.u
    submmnd
    anim12ci
    @3
    @9
    @21
    @25
    @3
    cX
    @7
    @8
    wf
    #
    @9
    @0
    cS
    cbs
    cfv
    #
    @7
    cF
    wf
    cX
    @27
    wss
    #
    @26
    @2
    @27
    @7
    cS
    cT
    cF
    @27
    eqid
    #
    @7
    eqid
    #
    mhmf
    @27
    cX
    cS
    @29
    submss
    #
    @27
    @7
    cX
    cF
    fssres
    syl2an
    @3
    cX
    @6
    @7
    @8
    @3
    @28
    cX
    @6
    wceq
    @2
    @28
    @0
    @31
    adantl
    cX
    @27
    cU
    cS
    resmhm.u
    @29
    ressbas2
    syl
    #
    feq2d
    mpbid
    @3
    @10
    @11
    cS
    cplusg
    cfv
    #
    co
    #
    @8
    cfv
    #
    @18
    wceq
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    @21
    @3
    @36
    vx
    vy
    cX
    cX
    @3
    @10
    cX
    wcel
    #
    @11
    cX
    wcel
    #
    wa
    #
    wa
    #
    @34
    cF
    cfv
    #
    @10
    cF
    cfv
    #
    @11
    cF
    cfv
    #
    @17
    co
    #
    @35
    @18
    @41
    @0
    @10
    @27
    wcel
    @11
    @27
    wcel
    @42
    @45
    wceq
    @0
    @2
    @40
    simpll
    @41
    cX
    @27
    @10
    @2
    @28
    @0
    @40
    @31
    ad2antlr
    #
    @3
    @38
    @39
    simprl
    sseldd
    @41
    cX
    @27
    @11
    @46
    @3
    @38
    @39
    simprr
    sseldd
    @27
    @33
    @17
    cS
    cT
    cF
    @10
    @11
    @29
    @33
    eqid
    #
    @17
    eqid
    #
    mhmlin
    syl3anc
    @41
    @34
    cX
    wcel
    #
    @35
    @42
    wceq
    @2
    @40
    @49
    @0
    @2
    @38
    @39
    @49
    @33
    cX
    cS
    @10
    @11
    @47
    submcl
    3expb
    adantll
    @34
    cX
    cF
    fvres
    syl
    @40
    @18
    @45
    wceq
    @3
    @38
    @39
    @15
    @43
    @16
    @44
    @17
    @10
    cX
    cF
    fvres
    @11
    cX
    cF
    fvres
    oveqan12d
    adantl
    3eqtr4d
    ralrimivva
    @3
    @37
    @20
    vx
    cX
    @6
    @32
    @3
    @36
    @19
    vy
    cX
    @6
    @32
    @3
    @35
    @14
    @18
    @3
    @34
    @13
    @8
    @3
    @33
    @12
    @10
    @11
    @2
    @33
    @12
    wceq
    @0
    cX
    @33
    cS
    cU
    @1
    resmhm.u
    @47
    ressplusg
    adantl
    oveqd
    fveq2d
    eqeq1d
    raleqbidv
    raleqbidv
    mpbid
    @3
    cS
    c0g
    cfv
    #
    @8
    cfv
    #
    @50
    cF
    cfv
    #
    @23
    @24
    @3
    @50
    cX
    wcel
    #
    @51
    @52
    wceq
    @2
    @53
    @0
    cX
    cS
    @50
    @50
    eqid
    #
    subm0cl
    adantl
    @50
    cX
    cF
    fvres
    syl
    @3
    @50
    @22
    @8
    @2
    @50
    @22
    wceq
    @0
    cX
    cU
    cS
    @50
    resmhm.u
    @54
    subm0
    adantl
    fveq2d
    @0
    @52
    @24
    wceq
    @2
    cS
    cT
    cF
    @24
    @50
    @54
    @24
    eqid
    #
    mhm0
    adantr
    3eqtr3d
    3jca
    vx
    vy
    @6
    @7
    @12
    @17
    cU
    cT
    @8
    @24
    @22
    @6
    eqid
    @30
    @12
    eqid
    @48
    @22
    eqid
    @55
    ismhm
    sylanbrc
end
