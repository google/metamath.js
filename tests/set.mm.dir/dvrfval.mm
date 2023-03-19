include "cdvr.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "cui.mm"
include "cinvr.mm"
include "cmulr.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "mpt2eq123dv.mm"
include "df-dvr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "eqid.mm"
include "mpt2eq12.mm"
include "sylancl.mm"
include "mpt20.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem dvrfval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let vr: setvar r
  let cX: class X
  let cY: class Y
  assume dvrval.b: |- B = ( Base ` R )
  assume dvrval.t: |- .x. = ( .r ` R )
  assume dvrval.u: |- U = ( Unit ` R )
  assume dvrval.i: |- I = ( invr ` R )
  assume dvrval.d: |- ./ = ( /r ` R )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint I x
  disjoint I y
  disjoint R x
  disjoint R y
  disjoint .x. x
  disjoint .x. y
  disjoint U x
  disjoint U y
  disjoint r x
  disjoint r y
  disjoint B r
  disjoint I r
  disjoint R r
  disjoint .x. r
  disjoint U r
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ./ = ( x e. B , y e. U |-> ( x .x. ( I ` y ) ) )

  proof
    c.dv
    cR
    cdvr
    cfv
    #
    vx
    vy
    cB
    cU
    vx
    cv
    #
    vy
    cv
    #
    cI
    cfv
    #
    c.x
    co
    #
    cmpt2
    #
    dvrval.d
    cR
    cvv
    wcel
    #
    @0
    @5
    wceq
    vr
    cR
    vx
    vy
    vr
    cv
    #
    cbs
    cfv
    #
    @7
    cui
    cfv
    #
    @1
    @2
    @7
    cinvr
    cfv
    #
    cfv
    #
    @7
    cmulr
    cfv
    #
    co
    #
    cmpt2
    @5
    cvv
    cdvr
    @7
    cR
    wceq
    #
    vx
    vy
    @8
    @9
    @13
    cB
    cU
    @4
    @14
    @8
    cR
    cbs
    cfv
    #
    cB
    @7
    cR
    cbs
    fveq2
    dvrval.b
    syl6eqr
    @14
    @9
    cR
    cui
    cfv
    #
    cU
    @7
    cR
    cui
    fveq2
    dvrval.u
    syl6eqr
    @14
    @1
    @1
    @11
    @3
    @12
    c.x
    @14
    @12
    cR
    cmulr
    cfv
    c.x
    @7
    cR
    cmulr
    fveq2
    dvrval.t
    syl6eqr
    @14
    @1
    eqidd
    @14
    @2
    @10
    cI
    @14
    @10
    cR
    cinvr
    cfv
    cI
    @7
    cR
    cinvr
    fveq2
    dvrval.i
    syl6eqr
    fveq1d
    oveq123d
    mpt2eq123dv
    vx
    vy
    vr
    df-dvr
    vx
    vy
    cB
    cU
    @4
    cB
    @15
    cvv
    dvrval.b
    cR
    cbs
    fvex
    eqeltri
    cU
    @16
    cvv
    dvrval.u
    cR
    cui
    fvex
    eqeltri
    mpt2ex
    fvmpt
    @6
    wn
    #
    @0
    c0
    @5
    cR
    cdvr
    fvprc
    @17
    @5
    vx
    vy
    c0
    cU
    @4
    cmpt2
    #
    c0
    @17
    cB
    c0
    wceq
    cU
    cU
    wceq
    @5
    @18
    wceq
    @17
    cB
    @15
    c0
    dvrval.b
    cR
    cbs
    fvprc
    syl5eq
    cU
    eqid
    vx
    vy
    cB
    cU
    c0
    cU
    @4
    mpt2eq12
    sylancl
    vx
    vy
    cU
    @4
    mpt20
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
