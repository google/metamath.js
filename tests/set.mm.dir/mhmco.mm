include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cmnd.mm"
include "cbs.mm"
include "cfv.mm"
include "ccom.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "mhmrcl2.mm"
include "mhmrcl1.mm"
include "anim12ci.mm"
include "eqid.mm"
include "mhmf.mm"
include "fco.mm"
include "syl2an.mm"
include "mhmlin.mm"
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
include "mndcl.mm"
include "sylan.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "mndidcl.mm"
include "syl.mm"
include "mhm0.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem mhmco
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. ( T MndHom U ) /\ G e. ( S MndHom T ) ) -> ( F o. G ) e. ( S MndHom U ) )

  proof
    cF
    cT
    cU
    cmhm
    co
    wcel
    #
    cG
    cS
    cT
    cmhm
    co
    wcel
    #
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
    cS
    c0g
    cfv
    #
    @7
    cfv
    #
    cU
    c0g
    cfv
    #
    wceq
    #
    w3a
    @7
    cS
    cU
    cmhm
    co
    wcel
    @0
    @4
    @1
    @3
    cT
    cU
    cF
    mhmrcl2
    cS
    cT
    cG
    mhmrcl1
    #
    anim12ci
    @2
    @8
    @19
    @23
    @0
    cT
    cbs
    cfv
    #
    @6
    cF
    wf
    @5
    @25
    cG
    wf
    #
    @8
    @1
    @25
    @6
    cT
    cU
    cF
    @25
    eqid
    #
    @6
    eqid
    #
    mhmf
    @5
    @25
    cS
    cT
    cG
    @5
    eqid
    #
    @27
    mhmf
    #
    @5
    @25
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
    @34
    @36
    @37
    @39
    cT
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @41
    @34
    @35
    @43
    cF
    @1
    @33
    @35
    @43
    wceq
    #
    @0
    @1
    @31
    @32
    @45
    @5
    @11
    @42
    cS
    cT
    cG
    @9
    @10
    @29
    @11
    eqid
    #
    @42
    eqid
    #
    mhmlin
    3expb
    adantll
    fveq2d
    @34
    @0
    @37
    @25
    wcel
    @39
    @25
    wcel
    @44
    @41
    wceq
    @0
    @1
    @33
    simpll
    @34
    @5
    @25
    @9
    cG
    @1
    @26
    @0
    @33
    @30
    ad2antlr
    #
    @2
    @31
    @32
    simprl
    #
    ffvelrnd
    @34
    @5
    @25
    @10
    cG
    @48
    @2
    @31
    @32
    simprr
    #
    ffvelrnd
    @25
    @42
    @16
    cT
    cU
    cF
    @37
    @39
    @27
    @47
    @16
    eqid
    #
    mhmlin
    syl3anc
    eqtrd
    @34
    @26
    @12
    @5
    wcel
    #
    @13
    @36
    wceq
    @48
    @2
    @3
    @33
    @52
    @1
    @3
    @0
    @24
    adantl
    #
    @3
    @31
    @32
    @52
    @5
    @11
    cS
    @9
    @10
    @29
    @46
    mndcl
    3expb
    sylan
    @5
    @25
    @12
    cF
    cG
    fvco3
    syl2anc
    @34
    @14
    @38
    @15
    @40
    @16
    @34
    @26
    @31
    @14
    @38
    wceq
    @48
    @49
    @5
    @25
    @9
    cF
    cG
    fvco3
    syl2anc
    @34
    @26
    @32
    @15
    @40
    wceq
    @48
    @50
    @5
    @25
    @10
    cF
    cG
    fvco3
    syl2anc
    oveq12d
    3eqtr4d
    ralrimivva
    @2
    @21
    @20
    cG
    cfv
    #
    cF
    cfv
    #
    cT
    c0g
    cfv
    #
    cF
    cfv
    #
    @22
    @2
    @26
    @20
    @5
    wcel
    #
    @21
    @55
    wceq
    @1
    @26
    @0
    @30
    adantl
    @2
    @3
    @58
    @53
    @5
    cS
    @20
    @29
    @20
    eqid
    #
    mndidcl
    syl
    @5
    @25
    @20
    cF
    cG
    fvco3
    syl2anc
    @2
    @54
    @56
    cF
    @1
    @54
    @56
    wceq
    @0
    cS
    cT
    cG
    @56
    @20
    @59
    @56
    eqid
    #
    mhm0
    adantl
    fveq2d
    @0
    @57
    @22
    wceq
    @1
    cT
    cU
    cF
    @22
    @56
    @60
    @22
    eqid
    #
    mhm0
    adantr
    3eqtrd
    3jca
    vx
    vy
    @5
    @6
    @11
    @16
    cS
    cU
    @7
    @22
    @20
    @29
    @28
    @46
    @51
    @59
    @61
    ismhm
    sylanbrc
end
