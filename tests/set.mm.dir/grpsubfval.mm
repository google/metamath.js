include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "csg.mm"
include "cbs.mm"
include "cminusg.mm"
include "cplusg.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "mpt2eq123dv.mm"
include "df-sbg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "mpt20.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem grpsubfval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vg: setvar g
  let cX: class X
  let cY: class Y
  assume grpsubval.b: |- B = ( Base ` G )
  assume grpsubval.p: |- .+ = ( +g ` G )
  assume grpsubval.i: |- I = ( invg ` G )
  assume grpsubval.m: |- .- = ( -g ` G )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint .+ x
  disjoint .+ y
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint G g
  disjoint I g
  disjoint .+ g
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- .- = ( x e. B , y e. B |-> ( x .+ ( I ` y ) ) )

  proof
    cG
    cvv
    wcel
    #
    c.mi
    vx
    vy
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    cI
    cfv
    #
    c.pl
    co
    #
    cmpt2
    #
    wceq
    @0
    c.mi
    cG
    csg
    cfv
    #
    @5
    grpsubval.m
    vg
    cG
    vx
    vy
    vg
    cv
    #
    cbs
    cfv
    #
    @8
    @1
    @2
    @7
    cminusg
    cfv
    #
    cfv
    #
    @7
    cplusg
    cfv
    #
    co
    #
    cmpt2
    @5
    cvv
    csg
    @7
    cG
    wceq
    #
    vx
    vy
    @8
    @8
    @12
    cB
    cB
    @4
    @13
    @8
    cG
    cbs
    cfv
    #
    cB
    @7
    cG
    cbs
    fveq2
    grpsubval.b
    syl6eqr
    #
    @15
    @13
    @1
    @1
    @10
    @3
    @11
    c.pl
    @13
    @11
    cG
    cplusg
    cfv
    c.pl
    @7
    cG
    cplusg
    fveq2
    grpsubval.p
    syl6eqr
    @13
    @1
    eqidd
    @13
    @2
    @9
    cI
    @13
    @9
    cG
    cminusg
    cfv
    cI
    @7
    cG
    cminusg
    fveq2
    grpsubval.i
    syl6eqr
    fveq1d
    oveq123d
    mpt2eq123dv
    vx
    vy
    vg
    df-sbg
    vx
    vy
    cB
    cB
    @4
    cB
    @14
    cvv
    grpsubval.b
    cG
    cbs
    fvex
    eqeltri
    #
    @16
    mpt2ex
    fvmpt
    syl5eq
    @0
    wn
    #
    c.mi
    c0
    @5
    @17
    c.mi
    @6
    c0
    grpsubval.m
    cG
    csg
    fvprc
    syl5eq
    @17
    @5
    vx
    vy
    c0
    c0
    @4
    cmpt2
    #
    c0
    @17
    cB
    c0
    wceq
    #
    @19
    @5
    @18
    wceq
    @17
    cB
    @14
    c0
    grpsubval.b
    cG
    cbs
    fvprc
    syl5eq
    #
    @20
    vx
    vy
    cB
    cB
    c0
    c0
    @4
    mpt2eq12
    syl2anc
    vx
    vy
    c0
    @4
    mpt20
    syl6eq
    eqtr4d
    pm2.61i
end
