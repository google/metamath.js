include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "c0g.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "cplusg.mm"
include "wceq.mm"
include "cbs.mm"
include "cgrp.mm"
include "csubg.mm"
include "nsgsubg.mm"
include "subgrcl.mm"
include "syl.mm"
include "eqid.mm"
include "grpidcl.mm"
include "qusadd.mm"
include "mpd3an23.mm"
include "grplid.mm"
include "syl2anc.mm"
include "eceq1d.mm"
include "eqtrd.mm"
include "wb.mm"
include "qusgrp.mm"
include "quseccl.mm"
include "mpdan.mm"
include "grpid.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem qus0
  let cS: class S
  let cG: class G
  let cH: class H
  let c.0: class .0.
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
  let cV: class V
  let cX: class X
  let cY: class Y
  assume qusgrp.h: |- H = ( G /s ( G ~QG S ) )
  assume qus0.p: |- .0. = ( 0g ` G )


  assert |- ( S e. ( NrmSGrp ` G ) -> [ .0. ] ( G ~QG S ) = ( 0g ` H ) )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    #
    cH
    c0g
    cfv
    #
    c.0
    cG
    cS
    cqg
    co
    #
    cec
    #
    @0
    @3
    @3
    cH
    cplusg
    cfv
    #
    co
    #
    @3
    wceq
    #
    @1
    @3
    wceq
    #
    @0
    @5
    c.0
    c.0
    cG
    cplusg
    cfv
    #
    co
    #
    @2
    cec
    #
    @3
    @0
    c.0
    cG
    cbs
    cfv
    #
    wcel
    #
    @12
    @5
    @10
    wceq
    @0
    cG
    cgrp
    wcel
    #
    @12
    @0
    cS
    cG
    csubg
    cfv
    wcel
    @13
    cS
    cG
    nsgsubg
    cS
    cG
    subgrcl
    syl
    #
    @11
    cG
    c.0
    @11
    eqid
    #
    qus0.p
    grpidcl
    syl
    #
    @16
    @8
    @4
    cS
    cG
    cH
    @11
    c.0
    c.0
    qusgrp.h
    @15
    @8
    eqid
    #
    @4
    eqid
    #
    qusadd
    mpd3an23
    @0
    @9
    c.0
    @2
    @0
    @13
    @12
    @9
    c.0
    wceq
    @14
    @16
    @11
    @8
    cG
    c.0
    c.0
    @15
    @17
    qus0.p
    grplid
    syl2anc
    eceq1d
    eqtrd
    @0
    cH
    cgrp
    wcel
    @3
    cH
    cbs
    cfv
    #
    wcel
    #
    @6
    @7
    wb
    cS
    cG
    cH
    qusgrp.h
    qusgrp
    @0
    @12
    @20
    @16
    @19
    cS
    cG
    cH
    @11
    c.0
    qusgrp.h
    @15
    @19
    eqid
    #
    quseccl
    mpdan
    @19
    @4
    cH
    @3
    @1
    @21
    @18
    @1
    eqid
    grpid
    syl2anc
    mpbid
    eqcomd
end
