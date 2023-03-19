include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "cplusg.mm"
include "cbs.mm"
include "eqid.mm"
include "csubg.mm"
include "cgrp.mm"
include "nsgsubg.mm"
include "subgrcl.mm"
include "syl.mm"
include "qusgrp.mm"
include "cv.mm"
include "cqg.mm"
include "co.mm"
include "cec.mm"
include "quseccl.mm"
include "fmptd.mm"
include "wa.mm"
include "wceq.mm"
include "qusadd.mm"
include "3expb.mm"
include "eceq1.mm"
include "cvv.mm"
include "ovex.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "fvmpt3i.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "grpcl.mm"
include "sylan.mm"
include "3eqtr4rd.mm"
include "isghmd.mm"

theorem qusghm
  let vx: setvar x
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume qusghm.x: |- X = ( Base ` G )
  assume qusghm.h: |- H = ( G /s ( G ~QG Y ) )
  assume qusghm.f: |- F = ( x e. X |-> [ x ] ( G ~QG Y ) )

  disjoint G x
  disjoint H x
  disjoint X x
  disjoint Y x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint x y
  disjoint x z
  disjoint G y
  disjoint G z
  disjoint H y
  disjoint H z
  disjoint X y
  disjoint X z
  disjoint Y y
  disjoint Y z
  assert |- ( Y e. ( NrmSGrp ` G ) -> F e. ( G GrpHom H ) )

  proof
    cY
    cG
    cnsg
    cfv
    wcel
    #
    vy
    vz
    cG
    cplusg
    cfv
    #
    cH
    cplusg
    cfv
    #
    cG
    cH
    cF
    cX
    cH
    cbs
    cfv
    #
    qusghm.x
    @3
    eqid
    #
    @1
    eqid
    #
    @2
    eqid
    #
    @0
    cY
    cG
    csubg
    cfv
    wcel
    cG
    cgrp
    wcel
    #
    cY
    cG
    nsgsubg
    cY
    cG
    subgrcl
    syl
    #
    cY
    cG
    cH
    qusghm.h
    qusgrp
    @0
    vx
    cX
    vx
    cv
    #
    cG
    cY
    cqg
    co
    #
    cec
    #
    @3
    cF
    @3
    cY
    cG
    cH
    cX
    @9
    qusghm.h
    qusghm.x
    @4
    quseccl
    qusghm.f
    fmptd
    @0
    vy
    cv
    #
    cX
    wcel
    #
    vz
    cv
    #
    cX
    wcel
    #
    wa
    #
    wa
    #
    @12
    @10
    cec
    #
    @14
    @10
    cec
    #
    @2
    co
    #
    @12
    @14
    @1
    co
    #
    @10
    cec
    #
    @12
    cF
    cfv
    #
    @14
    cF
    cfv
    #
    @2
    co
    @21
    cF
    cfv
    #
    @0
    @13
    @15
    @20
    @22
    wceq
    @1
    @2
    cY
    cG
    cH
    cX
    @12
    @14
    qusghm.h
    qusghm.x
    @5
    @6
    qusadd
    3expb
    @17
    @23
    @18
    @24
    @19
    @2
    @13
    @23
    @18
    wceq
    @0
    @15
    vx
    @12
    @11
    @18
    cX
    cF
    @9
    @12
    @10
    eceq1
    qusghm.f
    @10
    cvv
    wcel
    @11
    cvv
    wcel
    cG
    cY
    cqg
    ovex
    @9
    cvv
    @10
    ecexg
    ax-mp
    #
    fvmpt3i
    ad2antrl
    @15
    @24
    @19
    wceq
    @0
    @13
    vx
    @14
    @11
    @19
    cX
    cF
    @9
    @14
    @10
    eceq1
    qusghm.f
    @26
    fvmpt3i
    ad2antll
    oveq12d
    @17
    @21
    cX
    wcel
    #
    @25
    @22
    wceq
    @0
    @7
    @16
    @27
    @8
    @7
    @13
    @15
    @27
    cX
    @1
    cG
    @12
    @14
    qusghm.x
    @5
    grpcl
    3expb
    sylan
    vx
    @21
    @11
    @22
    cX
    cF
    @9
    @21
    @10
    eceq1
    qusghm.f
    @26
    fvmpt3i
    syl
    3eqtr4rd
    isghmd
end
