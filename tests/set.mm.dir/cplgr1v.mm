include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "ccplgr.mm"
include "wcel.mm"
include "cv.mm"
include "cuvtx.mm"
include "wral.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "simpr.mm"
include "c0.mm"
include "ral0.mm"
include "wex.mm"
include "wi.mm"
include "cvv.mm"
include "wb.mm"
include "cvtx.mm"
include "fvexi.mm"
include "hash1snb.mm"
include "ax-mp.mm"
include "velsn.mm"
include "sneq.mm"
include "difeq2d.mm"
include "difid.mm"
include "syl6eq.mm"
include "sylbi.mm"
include "a1i.mm"
include "eleq2.mm"
include "difeq1.mm"
include "eqeq1d.mm"
include "3imtr4d.mm"
include "exlimiv.mm"
include "imp.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "uvtxel.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "cplgr1vlem.mm"
include "iscplgr.mm"
include "syl.mm"
include "mpbird.mm"

theorem cplgr1v
  let cG: class G
  let cV: class V
  let vv: setvar v
  let vn: setvar n
  assume cplgr0v.v: |- V = ( Vtx ` G )


  assert |- ( ( # ` V ) = 1 -> G e. ComplGraph )

  proof
    cV
    chash
    cfv
    c1
    wceq
    #
    cG
    ccplgr
    wcel
    #
    vv
    cv
    #
    cG
    cuvtx
    cfv
    wcel
    #
    vv
    cV
    wral
    #
    @0
    @3
    vv
    cV
    @0
    @2
    cV
    wcel
    #
    wa
    #
    @5
    vn
    cv
    #
    cG
    @2
    cnbgr
    co
    wcel
    #
    vn
    cV
    @2
    csn
    #
    cdif
    #
    wral
    #
    @3
    @0
    @5
    simpr
    @6
    @11
    @8
    vn
    c0
    wral
    @8
    vn
    ral0
    @6
    @8
    vn
    @10
    c0
    @0
    @5
    @10
    c0
    wceq
    #
    @0
    cV
    @7
    csn
    #
    wceq
    #
    vn
    wex
    #
    @5
    @12
    wi
    #
    cV
    cvv
    wcel
    @0
    @15
    wb
    cV
    cG
    cvtx
    cplgr0v.v
    fvexi
    cV
    cvv
    vn
    hash1snb
    ax-mp
    @14
    @16
    vn
    @14
    @2
    @13
    wcel
    #
    @13
    @9
    cdif
    #
    c0
    wceq
    #
    @5
    @12
    @17
    @19
    wi
    @14
    @17
    @2
    @7
    wceq
    #
    @19
    vv
    @7
    velsn
    @20
    @18
    @13
    @13
    cdif
    c0
    @20
    @9
    @13
    @13
    @2
    @7
    sneq
    difeq2d
    @13
    difid
    syl6eq
    sylbi
    a1i
    cV
    @13
    @2
    eleq2
    @14
    @10
    @18
    c0
    cV
    @13
    @9
    difeq1
    eqeq1d
    3imtr4d
    exlimiv
    sylbi
    imp
    raleqdv
    mpbiri
    vn
    cG
    @2
    cV
    cplgr0v.v
    uvtxel
    sylanbrc
    ralrimiva
    @0
    cG
    cvv
    wcel
    @1
    @4
    wb
    cG
    cV
    cplgr0v.v
    cplgr1vlem
    vv
    cG
    cV
    cvv
    cplgr0v.v
    iscplgr
    syl
    mpbird
end
