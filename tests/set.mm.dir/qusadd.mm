include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "cqg.mm"
include "co.mm"
include "cgrp.mm"
include "cqus.mm"
include "wceq.mm"
include "a1i.mm"
include "cbs.mm"
include "csubg.mm"
include "wer.mm"
include "nsgsubg.mm"
include "eqid.mm"
include "eqger.mm"
include "syl.mm"
include "subgrcl.mm"
include "cv.mm"
include "eqgcpbl.mm"
include "wa.mm"
include "grpcl.mm"
include "3expb.mm"
include "sylan.mm"
include "qusaddval.mm"

theorem qusadd
  let c.pl: class .+
  let c.pb: class .+b
  let cS: class S
  let cG: class G
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume qusgrp.h: |- H = ( G /s ( G ~QG S ) )
  assume qusadd.v: |- V = ( Base ` G )
  assume qusadd.p: |- .+ = ( +g ` G )
  assume qusadd.a: |- .+b = ( +g ` H )


  assert |- ( ( S e. ( NrmSGrp ` G ) /\ X e. V /\ Y e. V ) -> ( [ X ] ( G ~QG S ) .+b [ Y ] ( G ~QG S ) ) = [ ( X .+ Y ) ] ( G ~QG S ) )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    #
    cG
    cS
    cqg
    co
    #
    cG
    c.pb
    c.pl
    cH
    cV
    cX
    cY
    cgrp
    vq
    vp
    va
    vb
    cH
    cG
    @1
    cqus
    co
    wceq
    @0
    qusgrp.h
    a1i
    cV
    cG
    cbs
    cfv
    wceq
    @0
    qusadd.v
    a1i
    @0
    cS
    cG
    csubg
    cfv
    wcel
    #
    cV
    @1
    wer
    cS
    cG
    nsgsubg
    #
    @1
    cG
    cV
    cS
    qusadd.v
    @1
    eqid
    #
    eqger
    syl
    @0
    @2
    cG
    cgrp
    wcel
    #
    @3
    cS
    cG
    subgrcl
    syl
    #
    va
    cv
    vb
    cv
    vp
    cv
    #
    vq
    cv
    #
    c.pl
    @1
    cG
    cV
    cS
    qusadd.v
    @4
    qusadd.p
    eqgcpbl
    @0
    @5
    @7
    cV
    wcel
    #
    @8
    cV
    wcel
    #
    wa
    @7
    @8
    c.pl
    co
    cV
    wcel
    #
    @6
    @5
    @9
    @10
    @11
    cV
    c.pl
    cG
    @7
    @8
    qusadd.v
    qusadd.p
    grpcl
    3expb
    sylan
    qusadd.p
    qusadd.a
    qusaddval
end
