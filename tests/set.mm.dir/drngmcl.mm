include "cdr.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "co.mm"
include "cgrp.mm"
include "eqid.mm"
include "drngmgp.mm"
include "wss.mm"
include "cbs.mm"
include "wceq.mm"
include "difss.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "cvv.mm"
include "cplusg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "mp2b.mm"
include "grpcl.mm"
include "syl3an1.mm"

theorem drngmcl
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume drngmcl.b: |- B = ( Base ` R )
  assume drngmcl.t: |- .x. = ( .r ` R )
  assume drngmcl.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. DivRing /\ X e. ( B \ { .0. } ) /\ Y e. ( B \ { .0. } ) ) -> ( X .x. Y ) e. ( B \ { .0. } ) )

  proof
    cR
    cdr
    wcel
    cR
    cmgp
    cfv
    #
    cB
    c.0
    csn
    #
    cdif
    #
    cress
    co
    #
    cgrp
    wcel
    cX
    @2
    wcel
    cY
    @2
    wcel
    cX
    cY
    c.x
    co
    @2
    wcel
    cB
    cR
    @3
    c.0
    drngmcl.b
    drngmcl.z
    @3
    eqid
    #
    drngmgp
    @2
    c.x
    @3
    cX
    cY
    @2
    cB
    wss
    @2
    @3
    cbs
    cfv
    wceq
    cB
    @1
    difss
    @2
    cB
    @3
    @0
    @4
    cB
    cR
    @0
    @0
    eqid
    #
    drngmcl.b
    mgpbas
    ressbas2
    ax-mp
    cB
    cvv
    wcel
    @2
    cvv
    wcel
    c.x
    @3
    cplusg
    cfv
    wceq
    cB
    cR
    cbs
    cfv
    cvv
    drngmcl.b
    cR
    cbs
    fvex
    eqeltri
    cB
    @1
    cvv
    difexg
    @2
    c.x
    @0
    @3
    cvv
    @4
    cR
    c.x
    @0
    @5
    drngmcl.t
    mgpplusg
    ressplusg
    mp2b
    grpcl
    syl3an1
end
