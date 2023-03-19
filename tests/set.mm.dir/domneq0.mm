include "cdomn.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "3simpc.mm"
include "cnzr.mm"
include "isdomn.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "orbi1d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "orbi2d.mm"
include "rspc2va.mm"
include "syl2anc.mm"
include "crg.mm"
include "domnring.mm"
include "simp3.mm"
include "ringlz.mm"
include "syl5ibrcom.mm"
include "simp2.mm"
include "ringrz.mm"
include "jaod.mm"
include "impbid.mm"

theorem domneq0
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume domneq0.b: |- B = ( Base ` R )
  assume domneq0.t: |- .x. = ( .r ` R )
  assume domneq0.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Domn /\ X e. B /\ Y e. B ) -> ( ( X .x. Y ) = .0. <-> ( X = .0. \/ Y = .0. ) ) )

  proof
    cR
    cdomn
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.x
    co
    #
    c.0
    wceq
    #
    cX
    c.0
    wceq
    #
    cY
    c.0
    wceq
    #
    wo
    #
    @3
    @1
    @2
    wa
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    c.0
    wceq
    #
    @9
    c.0
    wceq
    #
    @10
    c.0
    wceq
    #
    wo
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @5
    @8
    wi
    #
    @0
    @1
    @2
    3simpc
    @0
    @1
    @17
    @2
    @0
    cR
    cnzr
    wcel
    @17
    vx
    vy
    cB
    cR
    c.x
    c.0
    domneq0.b
    domneq0.t
    domneq0.z
    isdomn
    simprbi
    3ad2ant1
    @16
    @18
    cX
    @10
    c.x
    co
    #
    c.0
    wceq
    #
    @6
    @14
    wo
    #
    wi
    vx
    vy
    cX
    cY
    cB
    cB
    @9
    cX
    wceq
    #
    @12
    @20
    @15
    @21
    @22
    @11
    @19
    c.0
    @9
    cX
    @10
    c.x
    oveq1
    eqeq1d
    @22
    @13
    @6
    @14
    @9
    cX
    c.0
    eqeq1
    orbi1d
    imbi12d
    @10
    cY
    wceq
    #
    @20
    @5
    @21
    @8
    @23
    @19
    @4
    c.0
    @10
    cY
    cX
    c.x
    oveq2
    eqeq1d
    @23
    @14
    @7
    @6
    @10
    cY
    c.0
    eqeq1
    orbi2d
    imbi12d
    rspc2va
    syl2anc
    @3
    @6
    @5
    @7
    @3
    @5
    @6
    c.0
    cY
    c.x
    co
    #
    c.0
    wceq
    #
    @3
    cR
    crg
    wcel
    #
    @2
    @25
    @0
    @1
    @26
    @2
    cR
    domnring
    3ad2ant1
    #
    @0
    @1
    @2
    simp3
    cB
    cR
    c.x
    cY
    c.0
    domneq0.b
    domneq0.t
    domneq0.z
    ringlz
    syl2anc
    @6
    @4
    @24
    c.0
    cX
    c.0
    cY
    c.x
    oveq1
    eqeq1d
    syl5ibrcom
    @3
    @5
    @7
    cX
    c.0
    c.x
    co
    #
    c.0
    wceq
    #
    @3
    @26
    @1
    @29
    @27
    @0
    @1
    @2
    simp2
    cB
    cR
    c.x
    cX
    c.0
    domneq0.b
    domneq0.t
    domneq0.z
    ringrz
    syl2anc
    @7
    @4
    @28
    c.0
    cY
    c.0
    cX
    c.x
    oveq2
    eqeq1d
    syl5ibrcom
    jaod
    impbid
end
