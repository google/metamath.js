include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wb.mm"
include "cbs.mm"
include "wral.mm"
include "cnsg.mm"
include "wss.mm"
include "id.mm"
include "ssnmz.mm"
include "wa.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "nmzsubg.mm"
include "syl.mm"
include "subsubg.mm"
include "mpbir2and.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "nmzbi.mm"
include "sylan2.mm"
include "rgen2a.mm"
include "wceq.mm"
include "subgbas.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "mpbii.mm"
include "eqid.mm"
include "cvv.mm"
include "cplusg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssexi.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "isnsg.mm"
include "sylanbrc.mm"

theorem nmznsg
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vw: setvar w
  assume elnmz.1: |- N = { x e. X | A. y e. X ( ( x .+ y ) e. S <-> ( y .+ x ) e. S ) }
  assume nmzsubg.2: |- X = ( Base ` G )
  assume nmzsubg.3: |- .+ = ( +g ` G )
  assume nmznsg.4: |- H = ( G |`s N )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint S x
  disjoint S y
  disjoint .+ x
  disjoint .+ y
  disjoint X x
  disjoint X y
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint y z
  disjoint G z
  disjoint N u
  disjoint N w
  disjoint N z
  disjoint S u
  disjoint S w
  disjoint S z
  disjoint .+ u
  disjoint .+ w
  disjoint .+ z
  disjoint H w
  disjoint H z
  disjoint X u
  disjoint X w
  disjoint X z
  assert |- ( S e. ( SubGrp ` G ) -> S e. ( NrmSGrp ` H ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cS
    cH
    csubg
    cfv
    wcel
    #
    vz
    cv
    #
    vw
    cv
    #
    c.pl
    co
    cS
    wcel
    @4
    @3
    c.pl
    co
    cS
    wcel
    wb
    #
    vw
    cH
    cbs
    cfv
    #
    wral
    #
    vz
    @6
    wral
    #
    cS
    cH
    cnsg
    cfv
    wcel
    @1
    @2
    @1
    cS
    cN
    wss
    #
    @1
    id
    vx
    vy
    c.pl
    cS
    cG
    cN
    cX
    elnmz.1
    nmzsubg.2
    nmzsubg.3
    ssnmz
    @1
    cN
    @0
    wcel
    #
    @2
    @1
    @9
    wa
    wb
    @1
    cG
    cgrp
    wcel
    @10
    cS
    cG
    subgrcl
    vx
    vy
    c.pl
    cS
    cG
    cN
    cX
    elnmz.1
    nmzsubg.2
    nmzsubg.3
    nmzsubg
    syl
    #
    cS
    cN
    cG
    cH
    nmznsg.4
    subsubg
    syl
    mpbir2and
    @1
    @5
    vw
    cN
    wral
    #
    vz
    cN
    wral
    @8
    @5
    vz
    vw
    cN
    @4
    cN
    wcel
    @3
    cN
    wcel
    @4
    cX
    wcel
    @5
    cN
    cX
    @4
    cN
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    cS
    wcel
    @14
    @13
    c.pl
    co
    cS
    wcel
    wb
    vy
    cX
    wral
    #
    vx
    cX
    crab
    cX
    elnmz.1
    @15
    vx
    cX
    ssrab2
    eqsstri
    #
    sseli
    vx
    vy
    @3
    @4
    c.pl
    cS
    cN
    cX
    elnmz.1
    nmzbi
    sylan2
    rgen2a
    @1
    @12
    @7
    vz
    cN
    @6
    @1
    @10
    cN
    @6
    wceq
    @11
    cN
    cG
    cH
    nmznsg.4
    subgbas
    syl
    #
    @1
    @5
    vw
    cN
    @6
    @17
    raleqdv
    raleqbidv
    mpbii
    vz
    vw
    c.pl
    cS
    cH
    @6
    @6
    eqid
    cN
    cvv
    wcel
    c.pl
    cH
    cplusg
    cfv
    wceq
    cN
    cX
    cX
    cG
    cbs
    cfv
    cvv
    nmzsubg.2
    cG
    cbs
    fvex
    eqeltri
    @16
    ssexi
    cN
    c.pl
    cG
    cH
    cvv
    nmznsg.4
    nmzsubg.3
    ressplusg
    ax-mp
    isnsg
    sylanbrc
end
