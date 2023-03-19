include "cmgmhm.mm"
include "co.mm"
include "wcel.mm"
include "csubmgm.mm"
include "cfv.mm"
include "wa.mm"
include "cmgm.mm"
include "cbs.mm"
include "cres.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "mgmhmrcl.mm"
include "simprd.mm"
include "submgmmgm.mm"
include "anim12ci.mm"
include "wss.mm"
include "eqid.mm"
include "mgmhmf.mm"
include "submgmss.mm"
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
include "mgmhmlin.mm"
include "syl3anc.mm"
include "submgmcl.mm"
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
include "jca.mm"
include "ismgmhm.mm"
include "sylanbrc.mm"

theorem resmgmhm
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume resmgmhm.u: |- U = ( S |`s X )


  assert |- ( ( F e. ( S MgmHom T ) /\ X e. ( SubMgm ` S ) ) -> ( F |` X ) e. ( U MgmHom T ) )

  proof
    cF
    cS
    cT
    cmgmhm
    co
    wcel
    #
    cX
    cS
    csubmgm
    cfv
    #
    wcel
    #
    wa
    #
    cU
    cmgm
    wcel
    #
    cT
    cmgm
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
    wa
    @8
    cU
    cT
    cmgmhm
    co
    wcel
    @0
    @5
    @2
    @4
    @0
    cS
    cmgm
    wcel
    @5
    cS
    cT
    cF
    mgmhmrcl
    simprd
    cX
    cU
    cS
    resmgmhm.u
    submgmmgm
    anim12ci
    @3
    @9
    @21
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
    @23
    wss
    #
    @22
    @2
    @23
    @7
    cS
    cT
    cF
    @23
    eqid
    #
    @7
    eqid
    #
    mgmhmf
    @23
    cX
    cS
    @25
    submgmss
    #
    @23
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
    @24
    cX
    @6
    wceq
    @2
    @24
    @0
    @27
    adantl
    cX
    @23
    cU
    cS
    resmgmhm.u
    @25
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
    @32
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
    @30
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
    @31
    @18
    @37
    @0
    @10
    @23
    wcel
    @11
    @23
    wcel
    @38
    @41
    wceq
    @0
    @2
    @36
    simpll
    @37
    cX
    @23
    @10
    @2
    @24
    @0
    @36
    @27
    ad2antlr
    #
    @3
    @34
    @35
    simprl
    sseldd
    @37
    cX
    @23
    @11
    @42
    @3
    @34
    @35
    simprr
    sseldd
    @23
    @29
    @17
    cS
    cT
    cF
    @10
    @11
    @25
    @29
    eqid
    #
    @17
    eqid
    #
    mgmhmlin
    syl3anc
    @37
    @30
    cX
    wcel
    #
    @31
    @38
    wceq
    @2
    @36
    @45
    @0
    @2
    @34
    @35
    @45
    @29
    cX
    cS
    @10
    @11
    @43
    submgmcl
    3expb
    adantll
    @30
    cX
    cF
    fvres
    syl
    @36
    @18
    @41
    wceq
    @3
    @34
    @35
    @15
    @39
    @16
    @40
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
    @33
    @20
    vx
    cX
    @6
    @28
    @3
    @32
    @19
    vy
    cX
    @6
    @28
    @3
    @31
    @14
    @18
    @3
    @30
    @13
    @8
    @3
    @29
    @12
    @10
    @11
    @2
    @29
    @12
    wceq
    @0
    cX
    @29
    cS
    cU
    @1
    resmgmhm.u
    @43
    ressplusg
    adantl
    oveqd
    fveq2d
    eqeq1d
    raleqbidv
    raleqbidv
    mpbid
    jca
    vx
    vy
    @6
    @7
    @12
    @17
    cU
    cT
    @8
    @6
    eqid
    @26
    @12
    eqid
    @44
    ismgmhm
    sylanbrc
end
