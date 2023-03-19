include "csrg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "c0g.mm"
include "cfv.mm"
include "ccmn.mm"
include "cmgp.mm"
include "cmnd.mm"
include "eqid.mm"
include "issrg.mm"
include "simp3bi.mm"
include "r19.21bi.mm"
include "simpld.mm"
include "3ad2antr1.mm"
include "simpr2.mm"
include "rsp.mm"
include "sylc.mm"
include "simpr3.mm"
include "caovdig.mm"
include "simprd.mm"
include "caovdirg.mm"
include "jca.mm"

theorem srgi
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume srgi.b: |- B = ( Base ` R )
  assume srgi.p: |- .+ = ( +g ` R )
  assume srgi.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. SRing /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .x. ( Y .+ Z ) ) = ( ( X .x. Y ) .+ ( X .x. Z ) ) /\ ( ( X .+ Y ) .x. Z ) = ( ( X .x. Z ) .+ ( Y .x. Z ) ) ) )

  proof
    cR
    csrg
    wcel
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    wa
    cX
    cY
    cZ
    c.pl
    co
    c.x
    co
    cX
    cY
    c.x
    co
    cX
    cZ
    c.x
    co
    #
    c.pl
    co
    wceq
    cX
    cY
    c.pl
    co
    cZ
    c.x
    co
    @1
    cY
    cZ
    c.x
    co
    c.pl
    co
    wceq
    @0
    vx
    vy
    vz
    cX
    cY
    cZ
    cB
    c.pl
    c.x
    c.pl
    cB
    @0
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    vz
    cv
    #
    cB
    wcel
    #
    w3a
    wa
    #
    @2
    @4
    @6
    c.pl
    co
    c.x
    co
    @2
    @4
    c.x
    co
    @2
    @6
    c.x
    co
    #
    c.pl
    co
    wceq
    #
    @2
    @4
    c.pl
    co
    @6
    c.x
    co
    @9
    @4
    @6
    c.x
    co
    c.pl
    co
    wceq
    #
    @8
    @10
    @11
    wa
    #
    vz
    cB
    wral
    #
    @7
    @12
    @8
    @13
    vy
    cB
    wral
    #
    @5
    @13
    @0
    @5
    @3
    @14
    @7
    @0
    @3
    wa
    @14
    cR
    c0g
    cfv
    #
    @2
    c.x
    co
    @15
    wceq
    @2
    @15
    c.x
    co
    @15
    wceq
    wa
    #
    @0
    @14
    @16
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
    @17
    vx
    cB
    wral
    vx
    vy
    vz
    cB
    c.pl
    cR
    c.x
    @18
    @15
    srgi.b
    @18
    eqid
    srgi.p
    srgi.t
    @15
    eqid
    issrg
    simp3bi
    r19.21bi
    simpld
    3ad2antr1
    @0
    @3
    @5
    @7
    simpr2
    @13
    vy
    cB
    rsp
    sylc
    @0
    @3
    @5
    @7
    simpr3
    @12
    vz
    cB
    rsp
    sylc
    #
    simpld
    caovdig
    @0
    vx
    vy
    vz
    cX
    cY
    cZ
    cB
    c.pl
    c.x
    c.pl
    cB
    @8
    @10
    @11
    @19
    simprd
    caovdirg
    jca
end
