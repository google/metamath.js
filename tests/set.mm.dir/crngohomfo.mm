include "ccring.mm"
include "wcel.mm"
include "crngo.mm"
include "wa.mm"
include "crnghom.mm"
include "co.mm"
include "wfo.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "simplr.mm"
include "wrex.mm"
include "wi.mm"
include "foelrn.mm"
include "ex.mm"
include "anim12d.mm"
include "reeanv.mm"
include "syl6ibr.mm"
include "ad2antll.mm"
include "w3a.mm"
include "eqid.mm"
include "crngocom.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "fveq2d.mm"
include "crngorngo.mm"
include "rngohommul.mm"
include "syl3anl1.mm"
include "ancom2s.mm"
include "3eqtr3d.mm"
include "oveq12.mm"
include "ancoms.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "3expa.mm"
include "adantrr.mm"
include "rexlimdvv.mm"
include "syld.mm"
include "ralrimivv.mm"
include "iscrngo2.mm"
include "sylanbrc.mm"

theorem crngohomfo
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume crnghomfo.1: |- G = ( 1st ` R )
  assume crnghomfo.2: |- X = ran G
  assume crnghomfo.3: |- J = ( 1st ` S )
  assume crnghomfo.4: |- Y = ran J


  assert |- ( ( ( R e. CRingOps /\ S e. RingOps ) /\ ( F e. ( R RngHom S ) /\ F : X -onto-> Y ) ) -> S e. CRingOps )

  proof
    cR
    ccring
    wcel
    #
    cS
    crngo
    wcel
    #
    wa
    #
    cF
    cR
    cS
    crnghom
    co
    wcel
    #
    cX
    cY
    cF
    wfo
    #
    wa
    #
    wa
    #
    @1
    vy
    cv
    #
    vz
    cv
    #
    cS
    c2nd
    cfv
    #
    co
    #
    @8
    @7
    @9
    co
    #
    wceq
    #
    vz
    cY
    wral
    vy
    cY
    wral
    cS
    ccring
    wcel
    @0
    @1
    @5
    simplr
    @6
    @12
    vy
    vz
    cY
    cY
    @6
    @7
    cY
    wcel
    #
    @8
    cY
    wcel
    #
    wa
    #
    @7
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @8
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    wa
    #
    vx
    cX
    wrex
    vw
    cX
    wrex
    #
    @12
    @4
    @15
    @23
    wi
    @2
    @3
    @4
    @15
    @18
    vw
    cX
    wrex
    #
    @21
    vx
    cX
    wrex
    #
    wa
    @23
    @4
    @13
    @24
    @14
    @25
    @4
    @13
    @24
    vw
    cX
    cY
    @7
    cF
    foelrn
    ex
    @4
    @14
    @25
    vx
    cX
    cY
    @8
    cF
    foelrn
    ex
    anim12d
    @18
    @21
    vw
    vx
    cX
    cX
    reeanv
    syl6ibr
    ad2antll
    @6
    @22
    @12
    vw
    vx
    cX
    cX
    @2
    @3
    @16
    cX
    wcel
    #
    @19
    cX
    wcel
    #
    wa
    #
    @22
    @12
    wi
    #
    wi
    #
    @4
    @0
    @1
    @3
    @30
    @0
    @1
    @3
    w3a
    #
    @28
    @29
    @31
    @28
    wa
    #
    @12
    @22
    @17
    @20
    @9
    co
    #
    @20
    @17
    @9
    co
    #
    wceq
    @32
    @16
    @19
    cR
    c2nd
    cfv
    #
    co
    #
    cF
    cfv
    #
    @19
    @16
    @35
    co
    #
    cF
    cfv
    #
    @33
    @34
    @32
    @36
    @38
    cF
    @0
    @1
    @28
    @36
    @38
    wceq
    #
    @3
    @0
    @26
    @27
    @40
    @16
    @19
    cR
    cG
    @35
    cX
    crnghomfo.1
    @35
    eqid
    #
    crnghomfo.2
    crngocom
    3expb
    3ad2antl1
    fveq2d
    @0
    cR
    crngo
    wcel
    #
    @1
    @3
    @28
    @37
    @33
    wceq
    cR
    crngorngo
    #
    @16
    @19
    cR
    cS
    cF
    cG
    @35
    @9
    cX
    crnghomfo.1
    crnghomfo.2
    @41
    @9
    eqid
    #
    rngohommul
    syl3anl1
    @0
    @42
    @1
    @3
    @28
    @39
    @34
    wceq
    #
    @43
    @42
    @1
    @3
    w3a
    @27
    @26
    @45
    @19
    @16
    cR
    cS
    cF
    cG
    @35
    @9
    cX
    crnghomfo.1
    crnghomfo.2
    @41
    @44
    rngohommul
    ancom2s
    syl3anl1
    3eqtr3d
    @22
    @10
    @33
    @11
    @34
    @7
    @17
    @8
    @20
    @9
    oveq12
    @21
    @18
    @11
    @34
    wceq
    @8
    @20
    @7
    @17
    @9
    oveq12
    ancoms
    eqeq12d
    syl5ibrcom
    ex
    3expa
    adantrr
    rexlimdvv
    syld
    ralrimivv
    vy
    vz
    cS
    cJ
    @9
    cY
    crnghomfo.3
    @44
    crnghomfo.4
    iscrngo2
    sylanbrc
end
