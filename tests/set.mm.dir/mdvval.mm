include "cmdv.mm"
include "cfv.mm"
include "cxp.mm"
include "cid.mm"
include "cdif.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cmvar.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "difeq1d.mm"
include "df-mdv.mm"
include "fvex.mm"
include "xpex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "fvmpt3i.mm"
include "wn.mm"
include "c0.mm"
include "0dif.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mdvval
  let cD: class D
  let cT: class T
  let cV: class V
  let vt: setvar t
  assume mdvval.v: |- V = ( mVR ` T )
  assume mdvval.d: |- D = ( mDV ` T )


  assert |- D = ( ( V X. V ) \ _I )

  proof
    cD
    cT
    cmdv
    cfv
    #
    cV
    cV
    cxp
    #
    cid
    cdif
    #
    mdvval.d
    cT
    cvv
    wcel
    #
    @0
    @2
    wceq
    vt
    cT
    vt
    cv
    #
    cmvar
    cfv
    #
    @5
    cxp
    #
    cid
    cdif
    #
    @2
    cvv
    cmdv
    @4
    cT
    wceq
    #
    @6
    @1
    cid
    @8
    @5
    cV
    @8
    @5
    cT
    cmvar
    cfv
    #
    cV
    @4
    cT
    cmvar
    fveq2
    mdvval.v
    syl6eqr
    sqxpeqd
    difeq1d
    vt
    df-mdv
    @6
    cvv
    wcel
    @7
    cvv
    wcel
    @5
    @5
    @4
    cmvar
    fvex
    #
    @10
    xpex
    @6
    cid
    cvv
    difexg
    ax-mp
    fvmpt3i
    @3
    wn
    #
    c0
    c0
    cid
    cdif
    #
    @0
    @2
    @12
    c0
    cid
    0dif
    eqcomi
    cT
    cmdv
    fvprc
    @11
    @1
    c0
    cid
    @11
    @1
    cV
    c0
    cxp
    c0
    @11
    cV
    c0
    cV
    @11
    cV
    @9
    c0
    mdvval.v
    cT
    cmvar
    fvprc
    syl5eq
    xpeq2d
    cV
    xp0
    syl6eq
    difeq1d
    3eqtr4a
    pm2.61i
    eqtri
end
