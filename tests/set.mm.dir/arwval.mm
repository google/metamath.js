include "carw.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "choma.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "unieqd.mm"
include "df-arw.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "uniex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "dmmptss.mm"
include "sseli.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl.mm"
include "cbs.mm"
include "cxp.mm"
include "csn.mm"
include "chom.mm"
include "cmpt.mm"
include "df-homa.mm"
include "syl5eq.mm"
include "rn0.mm"
include "syl6eq.mm"
include "uni0.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem arwval
  let cA: class A
  let cC: class C
  let cH: class H
  let vc: setvar c
  let vx: setvar x
  assume arwval.a: |- A = ( Arrow ` C )
  assume arwval.h: |- H = ( HomA ` C )


  assert |- A = U. ran H

  proof
    cA
    cC
    carw
    cfv
    #
    cH
    crn
    #
    cuni
    #
    arwval.a
    cC
    ccat
    wcel
    #
    @0
    @2
    wceq
    vc
    cC
    vc
    cv
    #
    choma
    cfv
    #
    crn
    #
    cuni
    #
    @2
    ccat
    carw
    @4
    cC
    wceq
    #
    @6
    @1
    @8
    @5
    cH
    @8
    @5
    cC
    choma
    cfv
    #
    cH
    @4
    cC
    choma
    fveq2
    arwval.h
    syl6eqr
    rneqd
    unieqd
    vc
    df-arw
    #
    @1
    cH
    cH
    @9
    cvv
    arwval.h
    cC
    choma
    fvex
    eqeltri
    rnex
    uniex
    fvmpt
    @3
    wn
    #
    @0
    c0
    @2
    @11
    cC
    carw
    cdm
    #
    wcel
    #
    wn
    @0
    c0
    wceq
    @13
    @3
    @12
    ccat
    cC
    vc
    ccat
    @7
    carw
    @10
    dmmptss
    sseli
    con3i
    cC
    carw
    ndmfv
    syl
    @11
    @2
    c0
    cuni
    c0
    @11
    @1
    c0
    @11
    @1
    c0
    crn
    c0
    @11
    cH
    c0
    @11
    cH
    @9
    c0
    arwval.h
    @11
    cC
    choma
    cdm
    #
    wcel
    #
    wn
    @9
    c0
    wceq
    @15
    @3
    @14
    ccat
    cC
    vc
    ccat
    vx
    @4
    cbs
    cfv
    #
    @16
    cxp
    vx
    cv
    #
    csn
    @17
    @4
    chom
    cfv
    cfv
    cxp
    cmpt
    choma
    vx
    vc
    df-homa
    dmmptss
    sseli
    con3i
    cC
    choma
    ndmfv
    syl
    syl5eq
    rneqd
    rn0
    syl6eq
    unieqd
    uni0
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
