include "crng.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmgm.mm"
include "co.mm"
include "csgrp.mm"
include "eqid.mm"
include "rngmgp.mm"
include "sgrpmgm.mm"
include "syl.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mgmcl.mm"
include "syl3an1.mm"

theorem rngcl
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume rngcl.b: |- B = ( Base ` R )
  assume rngcl.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Rng /\ X e. B /\ Y e. B ) -> ( X .x. Y ) e. B )

  proof
    cR
    crng
    wcel
    #
    cR
    cmgp
    cfv
    #
    cmgm
    wcel
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.x
    co
    cB
    wcel
    @0
    @1
    csgrp
    wcel
    @2
    cR
    @1
    @1
    eqid
    #
    rngmgp
    @1
    sgrpmgm
    syl
    cB
    @1
    cX
    cY
    c.x
    cB
    cR
    @1
    @3
    rngcl.b
    mgpbas
    cR
    c.x
    @1
    @3
    rngcl.t
    mgpplusg
    mgmcl
    syl3an1
end
