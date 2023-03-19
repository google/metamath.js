include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "cminusg.mm"
include "cplusg.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "quseccl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "qusinv.mm"
include "oveq2d.mm"
include "cgrp.mm"
include "csubg.mm"
include "nsgsubg.mm"
include "subgrcl.mm"
include "syl.mm"
include "grpinvcl.mm"
include "sylan.mm"
include "qusadd.mm"
include "syld3an3.mm"
include "3adant1.mm"
include "eceq1d.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem qussub
  let cS: class S
  let cG: class G
  let cH: class H
  let c.mi: class .-
  let cN: class N
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
  let c.pb: class .+b
  let c.pl: class .+
  assume qusgrp.h: |- H = ( G /s ( G ~QG S ) )
  assume qusinv.v: |- V = ( Base ` G )
  assume qussub.p: |- .- = ( -g ` G )
  assume qussub.a: |- N = ( -g ` H )


  assert |- ( ( S e. ( NrmSGrp ` G ) /\ X e. V /\ Y e. V ) -> ( [ X ] ( G ~QG S ) N [ Y ] ( G ~QG S ) ) = [ ( X .- Y ) ] ( G ~QG S ) )

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
    cY
    cV
    wcel
    #
    w3a
    #
    cX
    cG
    cS
    cqg
    co
    #
    cec
    #
    cY
    @4
    cec
    #
    cN
    co
    #
    @5
    @6
    cH
    cminusg
    cfv
    #
    cfv
    #
    cH
    cplusg
    cfv
    #
    co
    #
    @5
    cY
    cG
    cminusg
    cfv
    #
    cfv
    #
    @4
    cec
    #
    @10
    co
    #
    cX
    cY
    c.mi
    co
    #
    @4
    cec
    #
    @3
    @5
    cH
    cbs
    cfv
    #
    wcel
    #
    @6
    @18
    wcel
    #
    @7
    @11
    wceq
    @0
    @1
    @19
    @2
    @18
    cS
    cG
    cH
    cV
    cX
    qusgrp.h
    qusinv.v
    @18
    eqid
    #
    quseccl
    3adant3
    @0
    @2
    @20
    @1
    @18
    cS
    cG
    cH
    cV
    cY
    qusgrp.h
    qusinv.v
    @21
    quseccl
    3adant2
    @18
    @10
    cH
    @8
    cN
    @5
    @6
    @21
    @10
    eqid
    #
    @8
    eqid
    #
    qussub.a
    grpsubval
    syl2anc
    @3
    @9
    @14
    @5
    @10
    @0
    @2
    @9
    @14
    wceq
    @1
    cS
    cG
    cH
    @12
    @8
    cV
    cY
    qusgrp.h
    qusinv.v
    @12
    eqid
    #
    @23
    qusinv
    3adant2
    oveq2d
    @3
    @15
    cX
    @13
    cG
    cplusg
    cfv
    #
    co
    #
    @4
    cec
    #
    @17
    @0
    @1
    @2
    @13
    cV
    wcel
    #
    @15
    @27
    wceq
    @0
    @2
    @28
    @1
    @0
    cG
    cgrp
    wcel
    #
    @2
    @28
    @0
    cS
    cG
    csubg
    cfv
    wcel
    @29
    cS
    cG
    nsgsubg
    cS
    cG
    subgrcl
    syl
    cV
    cG
    @12
    cY
    qusinv.v
    @24
    grpinvcl
    sylan
    3adant2
    @25
    @10
    cS
    cG
    cH
    cV
    cX
    @13
    qusgrp.h
    qusinv.v
    @25
    eqid
    #
    @22
    qusadd
    syld3an3
    @3
    @16
    @26
    @4
    @1
    @2
    @16
    @26
    wceq
    @0
    cV
    @25
    cG
    @12
    c.mi
    cX
    cY
    qusinv.v
    @30
    @24
    qussub.p
    grpsubval
    3adant1
    eceq1d
    eqtr4d
    3eqtrd
end
