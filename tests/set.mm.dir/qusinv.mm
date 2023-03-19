include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "wceq.mm"
include "cplusg.mm"
include "c0g.mm"
include "cgrp.mm"
include "csubg.mm"
include "nsgsubg.mm"
include "subgrcl.mm"
include "syl.mm"
include "grpinvcl.mm"
include "sylan.mm"
include "eqid.mm"
include "qusadd.mm"
include "mpd3an3.mm"
include "grprinv.mm"
include "eceq1d.mm"
include "qus0.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "cbs.mm"
include "wb.mm"
include "qusgrp.mm"
include "quseccl.mm"
include "syldan.mm"
include "grpinvid1.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem qusinv
  let cS: class S
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
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
  assume qusinv.v: |- V = ( Base ` G )
  assume qusinv.i: |- I = ( invg ` G )
  assume qusinv.n: |- N = ( invg ` H )


  assert |- ( ( S e. ( NrmSGrp ` G ) /\ X e. V ) -> ( N ` [ X ] ( G ~QG S ) ) = [ ( I ` X ) ] ( G ~QG S ) )

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
    cN
    cfv
    cX
    cI
    cfv
    #
    @3
    cec
    #
    wceq
    #
    @4
    @6
    cH
    cplusg
    cfv
    #
    co
    #
    cH
    c0g
    cfv
    #
    wceq
    #
    @2
    @9
    cX
    @5
    cG
    cplusg
    cfv
    #
    co
    #
    @3
    cec
    #
    cG
    c0g
    cfv
    #
    @3
    cec
    #
    @10
    @0
    @1
    @5
    cV
    wcel
    #
    @9
    @14
    wceq
    @0
    cG
    cgrp
    wcel
    #
    @1
    @17
    @0
    cS
    cG
    csubg
    cfv
    wcel
    @18
    cS
    cG
    nsgsubg
    cS
    cG
    subgrcl
    syl
    #
    cV
    cG
    cI
    cX
    qusinv.v
    qusinv.i
    grpinvcl
    sylan
    #
    @12
    @8
    cS
    cG
    cH
    cV
    cX
    @5
    qusgrp.h
    qusinv.v
    @12
    eqid
    #
    @8
    eqid
    #
    qusadd
    mpd3an3
    @2
    @13
    @15
    @3
    @0
    @18
    @1
    @13
    @15
    wceq
    @19
    cV
    @12
    cG
    cI
    cX
    @15
    qusinv.v
    @21
    @15
    eqid
    #
    qusinv.i
    grprinv
    sylan
    eceq1d
    @0
    @16
    @10
    wceq
    @1
    cS
    cG
    cH
    @15
    qusgrp.h
    @23
    qus0
    adantr
    3eqtrd
    @2
    cH
    cgrp
    wcel
    #
    @4
    cH
    cbs
    cfv
    #
    wcel
    @6
    @25
    wcel
    #
    @7
    @11
    wb
    @0
    @24
    @1
    cS
    cG
    cH
    qusgrp.h
    qusgrp
    adantr
    @25
    cS
    cG
    cH
    cV
    cX
    qusgrp.h
    qusinv.v
    @25
    eqid
    #
    quseccl
    @0
    @1
    @17
    @26
    @20
    @25
    cS
    cG
    cH
    cV
    @5
    qusgrp.h
    qusinv.v
    @27
    quseccl
    syldan
    @25
    @8
    cH
    cN
    @4
    @6
    @10
    @27
    @22
    @10
    eqid
    qusinv.n
    grpinvid1
    syl3anc
    mpbird
end
