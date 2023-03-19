include "crg.mm"
include "wcel.mm"
include "crng.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "ringrng.mm"
include "wreu.mm"
include "ringideu.mm"
include "reurex.mm"
include "syl.mm"
include "jca.mm"
include "cgrp.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "cplusg.mm"
include "cabl.mm"
include "rngabl.mm"
include "ablgrp.mm"
include "adantr.mm"
include "csgrp.mm"
include "eqid.mm"
include "rngmgp.mm"
include "anim1i.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ismnddef.mm"
include "sylibr.mm"
include "isrng.mm"
include "simp3bi.mm"
include "isring.mm"
include "syl3anbrc.mm"
include "impbii.mm"

theorem isringrng
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let vz: setvar z
  let vk: setvar k
  assume isringrng.b: |- B = ( Base ` R )
  assume isringrng.t: |- .x. = ( .r ` R )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint .x. x
  disjoint .x. y
  disjoint B z
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint .x. z
  disjoint k x
  assert |- ( R e. Ring <-> ( R e. Rng /\ E. x e. B A. y e. B ( ( x .x. y ) = y /\ ( y .x. x ) = y ) ) )

  proof
    cR
    crg
    wcel
    #
    cR
    crng
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    @3
    wceq
    @3
    @2
    c.x
    co
    @3
    wceq
    wa
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    wa
    #
    @0
    @1
    @6
    cR
    ringrng
    @0
    @5
    vx
    cB
    wreu
    @6
    vy
    vx
    cB
    cR
    c.x
    isringrng.b
    isringrng.t
    ringideu
    @5
    vx
    cB
    reurex
    syl
    jca
    @7
    cR
    cgrp
    wcel
    #
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @2
    @3
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
    @4
    @2
    @11
    c.x
    co
    #
    @12
    co
    wceq
    @2
    @3
    @12
    co
    @11
    c.x
    co
    @13
    @3
    @11
    c.x
    co
    @12
    co
    wceq
    wa
    vz
    cB
    wral
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @0
    @1
    @8
    @6
    @1
    cR
    cabl
    wcel
    #
    @8
    cR
    rngabl
    cR
    ablgrp
    syl
    adantr
    @7
    @9
    csgrp
    wcel
    #
    @6
    wa
    @10
    @1
    @16
    @6
    cR
    @9
    @9
    eqid
    #
    rngmgp
    anim1i
    cB
    c.x
    vx
    @9
    vy
    cB
    cR
    @9
    @17
    isringrng.b
    mgpbas
    cR
    c.x
    @9
    @17
    isringrng.t
    mgpplusg
    ismnddef
    sylibr
    @1
    @14
    @6
    @1
    @15
    @16
    @14
    vx
    vy
    vz
    cB
    @12
    cR
    c.x
    @9
    isringrng.b
    @17
    @12
    eqid
    #
    isringrng.t
    isrng
    simp3bi
    adantr
    vx
    vy
    vz
    cB
    @12
    cR
    c.x
    @9
    isringrng.b
    @17
    @18
    isringrng.t
    isring
    syl3anbrc
    impbii
end
