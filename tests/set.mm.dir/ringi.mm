include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "cgrp.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "eqid.mm"
include "isring.mm"
include "simp3bi.mm"
include "adantr.mm"
include "simpr1.mm"
include "rsp.mm"
include "sylc.mm"
include "simpr2.mm"
include "simpr3.mm"
include "simpld.mm"
include "caovdig.mm"
include "simprd.mm"
include "caovdirg.mm"
include "jca.mm"

theorem ringi
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
  assume ringi.b: |- B = ( Base ` R )
  assume ringi.p: |- .+ = ( +g ` R )
  assume ringi.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .x. ( Y .+ Z ) ) = ( ( X .x. Y ) .+ ( X .x. Z ) ) /\ ( ( X .+ Y ) .x. Z ) = ( ( X .x. Z ) .+ ( Y .x. Z ) ) ) )

  proof
    cR
    crg
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
    #
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
    @10
    @4
    @6
    c.x
    co
    c.pl
    co
    wceq
    #
    @9
    @11
    @12
    wa
    #
    vz
    cB
    wral
    #
    @7
    @13
    @9
    @14
    vy
    cB
    wral
    #
    @5
    @14
    @9
    @15
    vx
    cB
    wral
    #
    @3
    @15
    @0
    @16
    @8
    @0
    cR
    cgrp
    wcel
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    @16
    vx
    vy
    vz
    cB
    c.pl
    cR
    c.x
    @17
    ringi.b
    @17
    eqid
    ringi.p
    ringi.t
    isring
    simp3bi
    adantr
    @0
    @3
    @5
    @7
    simpr1
    @15
    vx
    cB
    rsp
    sylc
    @0
    @3
    @5
    @7
    simpr2
    @14
    vy
    cB
    rsp
    sylc
    @0
    @3
    @5
    @7
    simpr3
    @13
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
    @9
    @11
    @12
    @18
    simprd
    caovdirg
    jca
end
