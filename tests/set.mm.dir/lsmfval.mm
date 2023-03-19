include "wcel.mm"
include "clsm.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "crn.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cbs.mm"
include "cplusg.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "oveqd.mm"
include "mpt2eq3dv.mm"
include "rneqd.mm"
include "mpt2eq123dv.mm"
include "df-lsm.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem lsmfval
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vt: setvar t
  let cB: class B
  let c.pl: class .+
  let c.po: class .(+)
  let cG: class G
  let cV: class V
  let vw: setvar w
  let vz: setvar z
  let cT: class T
  let cX: class X
  let cU: class U
  let cY: class Y
  assume lsmfval.v: |- B = ( Base ` G )
  assume lsmfval.a: |- .+ = ( +g ` G )
  assume lsmfval.s: |- .(+) = ( LSSum ` G )

  disjoint t u
  disjoint t x
  disjoint t y
  disjoint .+ t
  disjoint u x
  disjoint u y
  disjoint .+ u
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint B t
  disjoint B u
  disjoint B x
  disjoint B y
  disjoint G t
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint t w
  disjoint t z
  disjoint u w
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint x z
  disjoint y z
  disjoint .+ z
  disjoint B w
  disjoint B z
  disjoint T t
  disjoint T u
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint G w
  disjoint G z
  disjoint U t
  disjoint U u
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint Y x
  disjoint Y y
  assert |- ( G e. V -> .(+) = ( t e. ~P B , u e. ~P B |-> ran ( x e. t , y e. u |-> ( x .+ y ) ) ) )

  proof
    cG
    cV
    wcel
    #
    c.po
    cG
    clsm
    cfv
    #
    vt
    vu
    cB
    cpw
    #
    @2
    vx
    vy
    vt
    cv
    #
    vu
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cmpt2
    #
    crn
    #
    cmpt2
    #
    lsmfval.s
    @0
    cG
    cvv
    wcel
    @1
    @10
    wceq
    cG
    cV
    elex
    vw
    cG
    vt
    vu
    vw
    cv
    #
    cbs
    cfv
    #
    cpw
    #
    @13
    vx
    vy
    @3
    @4
    @5
    @6
    @11
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    crn
    #
    cmpt2
    @10
    cvv
    clsm
    @11
    cG
    wceq
    #
    vt
    vu
    @13
    @13
    @17
    @2
    @2
    @9
    @18
    @12
    cB
    @18
    @12
    cG
    cbs
    cfv
    #
    cB
    @11
    cG
    cbs
    fveq2
    lsmfval.v
    syl6eqr
    pweqd
    #
    @20
    @18
    @16
    @8
    @18
    vx
    vy
    @3
    @4
    @15
    @7
    @18
    @14
    c.pl
    @5
    @6
    @18
    @14
    cG
    cplusg
    cfv
    c.pl
    @11
    cG
    cplusg
    fveq2
    lsmfval.a
    syl6eqr
    oveqd
    mpt2eq3dv
    rneqd
    mpt2eq123dv
    vx
    vy
    vw
    vu
    vt
    df-lsm
    vt
    vu
    @2
    @2
    @9
    cB
    cB
    @19
    cvv
    lsmfval.v
    cG
    cbs
    fvex
    eqeltri
    pwex
    #
    @21
    mpt2ex
    fvmpt
    syl
    syl5eq
end
