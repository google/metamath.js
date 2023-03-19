include "cmvh.mm"
include "cfv.mm"
include "cv.mm"
include "cs1.mm"
include "cop.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cmvar.mm"
include "cmty.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "opeq1d.mm"
include "mpteq12dv.mm"
include "df-mvh.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "mpt0.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mvhfval
  let vv: setvar v
  let cT: class T
  let cH: class H
  let cV: class V
  let cY: class Y
  let vt: setvar t
  let cX: class X
  assume mvhfval.v: |- V = ( mVR ` T )
  assume mvhfval.y: |- Y = ( mType ` T )
  assume mvhfval.h: |- H = ( mVH ` T )

  disjoint T v
  disjoint V v
  disjoint Y v
  disjoint t v
  disjoint T t
  disjoint V t
  disjoint X v
  disjoint Y t
  assert |- H = ( v e. V |-> <. ( Y ` v ) , <" v "> >. )

  proof
    cH
    cT
    cmvh
    cfv
    #
    vv
    cV
    vv
    cv
    #
    cY
    cfv
    #
    @1
    cs1
    #
    cop
    #
    cmpt
    #
    mvhfval.h
    cT
    cvv
    wcel
    #
    @0
    @5
    wceq
    vt
    cT
    vv
    vt
    cv
    #
    cmvar
    cfv
    #
    @1
    @7
    cmty
    cfv
    #
    cfv
    #
    @3
    cop
    #
    cmpt
    @5
    cvv
    cmvh
    @7
    cT
    wceq
    #
    vv
    @8
    @11
    cV
    @4
    @12
    @8
    cT
    cmvar
    cfv
    #
    cV
    @7
    cT
    cmvar
    fveq2
    mvhfval.v
    syl6eqr
    @12
    @10
    @2
    @3
    @12
    @1
    @9
    cY
    @12
    @9
    cT
    cmty
    cfv
    cY
    @7
    cT
    cmty
    fveq2
    mvhfval.y
    syl6eqr
    fveq1d
    opeq1d
    mpteq12dv
    vv
    vt
    df-mvh
    vv
    cV
    @4
    cV
    @13
    cvv
    mvhfval.v
    cT
    cmvar
    fvex
    eqeltri
    mptex
    fvmpt
    @6
    wn
    #
    c0
    vv
    c0
    @4
    cmpt
    #
    @0
    @5
    @15
    c0
    vv
    @4
    mpt0
    eqcomi
    cT
    cmvh
    fvprc
    @14
    vv
    cV
    c0
    @4
    @14
    cV
    @13
    c0
    mvhfval.v
    cT
    cmvar
    fvprc
    syl5eq
    mpteq1d
    3eqtr4a
    pm2.61i
    eqtri
end
