include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "cqs.mm"
include "ovex.mm"
include "ecelqsi.mm"
include "adantl.mm"
include "cbs.mm"
include "cvv.mm"
include "cgrp.mm"
include "cqus.mm"
include "wceq.mm"
include "a1i.mm"
include "csubg.mm"
include "nsgsubg.mm"
include "subgrcl.mm"
include "syl.mm"
include "adantr.mm"
include "qusbas.mm"
include "syl6eqr.mm"
include "eleqtrd.mm"

theorem quseccl
  let cB: class B
  let cS: class S
  let cG: class G
  let cH: class H
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let c.pb: class .+b
  let c.pl: class .+
  let cY: class Y
  assume qusgrp.h: |- H = ( G /s ( G ~QG S ) )
  assume qusadd.v: |- V = ( Base ` G )
  assume quseccl.b: |- B = ( Base ` H )


  assert |- ( ( S e. ( NrmSGrp ` G ) /\ X e. V ) -> [ X ] ( G ~QG S ) e. B )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cX
    cG
    cS
    cqg
    co
    #
    cec
    #
    cV
    @3
    cqs
    #
    cB
    @1
    @4
    @5
    wcel
    @0
    cV
    cX
    @3
    cG
    cS
    cqg
    ovex
    #
    ecelqsi
    adantl
    @2
    @5
    cH
    cbs
    cfv
    cB
    @2
    @3
    cG
    cH
    cV
    cvv
    cgrp
    cH
    cG
    @3
    cqus
    co
    wceq
    @2
    qusgrp.h
    a1i
    cV
    cG
    cbs
    cfv
    wceq
    @2
    qusadd.v
    a1i
    @3
    cvv
    wcel
    @2
    @6
    a1i
    @0
    cG
    cgrp
    wcel
    #
    @1
    @0
    cS
    cG
    csubg
    cfv
    wcel
    @7
    cS
    cG
    nsgsubg
    cS
    cG
    subgrcl
    syl
    adantr
    qusbas
    quseccl.b
    syl6eqr
    eleqtrd
end
