include "cmgmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cmgm.mm"
include "cbs.mm"
include "cfv.mm"
include "ccom.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "mgmhmrcl.mm"
include "simprd.mm"
include "simpld.mm"
include "anim12ci.mm"
include "eqid.mm"
include "mgmhmf.mm"
include "fco.mm"
include "syl2an.mm"
include "mgmhmlin.mm"
include "3expb.mm"
include "adantll.mm"
include "fveq2d.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "adantl.mm"
include "mgmcl.mm"
include "sylan.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "jca.mm"
include "ismgmhm.mm"
include "sylanbrc.mm"

theorem mgmhmco
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( ( F e. ( T MgmHom U ) /\ G e. ( S MgmHom T ) ) -> ( F o. G ) e. ( S MgmHom U ) )

  proof
    cF
    cT
    cU
    cmgmhm
    co
    wcel
    #
    cG
    cS
    cT
    cmgmhm
    co
    wcel
    #
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
    cG
    ccom
    #
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
    #
    @7
    cfv
    #
    @9
    @7
    cfv
    #
    @10
    @7
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
    @5
    wral
    vx
    @5
    wral
    #
    wa
    @7
    cS
    cU
    cmgmhm
    co
    wcel
    @0
    @4
    @1
    @3
    @0
    cT
    cmgm
    wcel
    #
    @4
    cT
    cU
    cF
    mgmhmrcl
    simprd
    @1
    @3
    @20
    cS
    cT
    cG
    mgmhmrcl
    simpld
    #
    anim12ci
    @2
    @8
    @19
    @0
    cT
    cbs
    cfv
    #
    @6
    cF
    wf
    @5
    @22
    cG
    wf
    #
    @8
    @1
    @22
    @6
    cT
    cU
    cF
    @22
    eqid
    #
    @6
    eqid
    #
    mgmhmf
    @5
    @22
    cS
    cT
    cG
    @5
    eqid
    #
    @24
    mgmhmf
    #
    @5
    @22
    @6
    cF
    cG
    fco
    syl2an
    @2
    @18
    vx
    vy
    @5
    @5
    @2
    @9
    @5
    wcel
    #
    @10
    @5
    wcel
    #
    wa
    #
    wa
    #
    @12
    cG
    cfv
    #
    cF
    cfv
    #
    @9
    cG
    cfv
    #
    cF
    cfv
    #
    @10
    cG
    cfv
    #
    cF
    cfv
    #
    @16
    co
    #
    @13
    @17
    @31
    @33
    @34
    @36
    cT
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @38
    @31
    @32
    @40
    cF
    @1
    @30
    @32
    @40
    wceq
    #
    @0
    @1
    @28
    @29
    @42
    @5
    @11
    @39
    cS
    cT
    cG
    @9
    @10
    @26
    @11
    eqid
    #
    @39
    eqid
    #
    mgmhmlin
    3expb
    adantll
    fveq2d
    @31
    @0
    @34
    @22
    wcel
    @36
    @22
    wcel
    @41
    @38
    wceq
    @0
    @1
    @30
    simpll
    @31
    @5
    @22
    @9
    cG
    @1
    @23
    @0
    @30
    @27
    ad2antlr
    #
    @2
    @28
    @29
    simprl
    #
    ffvelrnd
    @31
    @5
    @22
    @10
    cG
    @45
    @2
    @28
    @29
    simprr
    #
    ffvelrnd
    @22
    @39
    @16
    cT
    cU
    cF
    @34
    @36
    @24
    @44
    @16
    eqid
    #
    mgmhmlin
    syl3anc
    eqtrd
    @31
    @23
    @12
    @5
    wcel
    #
    @13
    @33
    wceq
    @45
    @2
    @3
    @30
    @49
    @1
    @3
    @0
    @21
    adantl
    @3
    @28
    @29
    @49
    @5
    cS
    @9
    @10
    @11
    @26
    @43
    mgmcl
    3expb
    sylan
    @5
    @22
    @12
    cF
    cG
    fvco3
    syl2anc
    @31
    @14
    @35
    @15
    @37
    @16
    @31
    @23
    @28
    @14
    @35
    wceq
    @45
    @46
    @5
    @22
    @9
    cF
    cG
    fvco3
    syl2anc
    @31
    @23
    @29
    @15
    @37
    wceq
    @45
    @47
    @5
    @22
    @10
    cF
    cG
    fvco3
    syl2anc
    oveq12d
    3eqtr4d
    ralrimivva
    jca
    vx
    vy
    @5
    @6
    @11
    @16
    cS
    cU
    @7
    @26
    @25
    @43
    @48
    ismgmhm
    sylanbrc
end
