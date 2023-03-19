include "csrg.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "ccmn.mm"
include "cmgp.mm"
include "cmnd.mm"
include "eqid.mm"
include "issrg.mm"
include "simp3bi.mm"
include "r19.21bi.mm"
include "simprld.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "mpan9.mm"

theorem srglz
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume srgz.b: |- B = ( Base ` R )
  assume srgz.t: |- .x. = ( .r ` R )
  assume srgz.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. SRing /\ X e. B ) -> ( .0. .x. X ) = .0. )

  proof
    cR
    csrg
    wcel
    #
    c.0
    vx
    cv
    #
    c.x
    co
    #
    c.0
    wceq
    #
    vx
    cB
    wral
    cX
    cB
    wcel
    c.0
    cX
    c.x
    co
    #
    c.0
    wceq
    #
    @0
    @3
    vx
    cB
    @0
    @1
    cB
    wcel
    wa
    @1
    vy
    cv
    #
    vz
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    c.x
    co
    @1
    @6
    c.x
    co
    @1
    @7
    c.x
    co
    #
    @8
    co
    wceq
    @1
    @6
    @8
    co
    @7
    c.x
    co
    @9
    @6
    @7
    c.x
    co
    @8
    co
    wceq
    wa
    vz
    cB
    wral
    vy
    cB
    wral
    #
    @3
    @1
    c.0
    c.x
    co
    c.0
    wceq
    #
    @0
    @10
    @3
    @11
    wa
    wa
    #
    vx
    cB
    @0
    cR
    ccmn
    wcel
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    @12
    vx
    cB
    wral
    vx
    vy
    vz
    cB
    @8
    cR
    c.x
    @13
    c.0
    srgz.b
    @13
    eqid
    @8
    eqid
    srgz.t
    srgz.z
    issrg
    simp3bi
    r19.21bi
    simprld
    ralrimiva
    @3
    @5
    vx
    cX
    cB
    @1
    cX
    wceq
    @2
    @4
    c.0
    @1
    cX
    c.0
    c.x
    oveq2
    eqeq1d
    rspcv
    mpan9
end
