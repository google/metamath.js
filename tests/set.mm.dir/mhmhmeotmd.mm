include "ctmd.mm"
include "wcel.mm"
include "cmnd.mm"
include "ctps.mm"
include "cplusf.mm"
include "cfv.mm"
include "ctopn.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "cmhm.mm"
include "mhmrcl2.mm"
include "ax-mp.mm"
include "cbs.mm"
include "cxp.mm"
include "wf.mm"
include "mhmrcl1.mm"
include "eqid.mm"
include "mndplusf.mm"
include "ctopon.mm"
include "tmdtopon.mm"
include "istps.mm"
include "mpbi.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "wceq.mm"
include "mhmlin.mm"
include "mp3an1.mm"
include "plusfval.mm"
include "fveq2d.mm"
include "mhmf.mm"
include "ffvelrni.mm"
include "syl2an.mm"
include "3eqtr4d.mm"
include "tmdcn.mm"
include "mndpluscn.mm"
include "istmd.mm"
include "mpbir3an.mm"

theorem mhmhmeotmd
  let cS: class S
  let cT: class T
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume mhmhmeotmd.m: |- F e. ( S MndHom T )
  assume mhmhmeotmd.h: |- F e. ( ( TopOpen ` S ) Homeo ( TopOpen ` T ) )
  assume mhmhmeotmd.t: |- S e. TopMnd
  assume mhmhmeotmd.s: |- T e. TopSp


  assert |- T e. TopMnd

  proof
    cT
    ctmd
    wcel
    cT
    cmnd
    wcel
    #
    cT
    ctps
    wcel
    #
    cT
    cplusf
    cfv
    #
    cT
    ctopn
    cfv
    #
    @3
    ctx
    co
    @3
    ccn
    co
    wcel
    cF
    cS
    cT
    cmhm
    co
    wcel
    #
    @0
    mhmhmeotmd.m
    cS
    cT
    cF
    mhmrcl2
    ax-mp
    #
    mhmhmeotmd.s
    vx
    vy
    cS
    cbs
    cfv
    #
    cT
    cbs
    cfv
    #
    cS
    cplusf
    cfv
    #
    cF
    @2
    cS
    ctopn
    cfv
    #
    @3
    mhmhmeotmd.h
    cS
    cmnd
    wcel
    #
    @6
    @6
    cxp
    @6
    @8
    wf
    @4
    @10
    mhmhmeotmd.m
    cS
    cT
    cF
    mhmrcl1
    ax-mp
    @6
    @8
    cS
    @6
    eqid
    #
    @8
    eqid
    #
    mndplusf
    ax-mp
    @0
    @7
    @7
    cxp
    @7
    @2
    wf
    @5
    @7
    @2
    cT
    @7
    eqid
    #
    @2
    eqid
    #
    mndplusf
    ax-mp
    cS
    ctmd
    wcel
    #
    @9
    @6
    ctopon
    cfv
    wcel
    mhmhmeotmd.t
    cS
    @9
    @6
    @9
    eqid
    #
    @11
    tmdtopon
    ax-mp
    @1
    @3
    @7
    ctopon
    cfv
    wcel
    mhmhmeotmd.s
    @7
    @3
    cT
    @13
    @3
    eqid
    #
    istps
    mpbi
    vx
    cv
    #
    @6
    wcel
    #
    vy
    cv
    #
    @6
    wcel
    #
    wa
    #
    @18
    @20
    cS
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @18
    cF
    cfv
    #
    @20
    cF
    cfv
    #
    cT
    cplusg
    cfv
    #
    co
    #
    @18
    @20
    @8
    co
    #
    cF
    cfv
    @26
    @27
    @2
    co
    #
    @4
    @19
    @21
    @25
    @29
    wceq
    mhmhmeotmd.m
    @6
    @23
    @28
    cS
    cT
    cF
    @18
    @20
    @11
    @23
    eqid
    #
    @28
    eqid
    #
    mhmlin
    mp3an1
    @22
    @30
    @24
    cF
    @6
    @23
    @8
    cS
    @18
    @20
    @11
    @32
    @12
    plusfval
    fveq2d
    @19
    @26
    @7
    wcel
    @27
    @7
    wcel
    @31
    @29
    wceq
    @21
    @6
    @7
    @18
    cF
    @4
    @6
    @7
    cF
    wf
    mhmhmeotmd.m
    @6
    @7
    cS
    cT
    cF
    @11
    @13
    mhmf
    ax-mp
    #
    ffvelrni
    @6
    @7
    @20
    cF
    @34
    ffvelrni
    @7
    @28
    @2
    cT
    @26
    @27
    @13
    @33
    @14
    plusfval
    syl2an
    3eqtr4d
    @15
    @8
    @9
    @9
    ctx
    co
    @9
    ccn
    co
    wcel
    mhmhmeotmd.t
    @8
    cS
    @9
    @16
    @12
    tmdcn
    ax-mp
    mndpluscn
    @2
    cT
    @3
    @14
    @17
    istmd
    mpbir3an
end
