include "cusgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "cvtx.mm"
include "wreu.mm"
include "ciedg.mm"
include "cdm.mm"
include "wrex.mm"
include "wi.mm"
include "cuhgr.mm"
include "wb.mm"
include "usgruhgr.mm"
include "eqid.mm"
include "uhgredgiedgb.mm"
include "syl.mm"
include "w3a.mm"
include "usgredgreu.mm"
include "3expia.mm"
include "3adant3.mm"
include "eleq2.mm"
include "eqeq1.mm"
include "reubidv.mm"
include "imbi12d.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "sylbid.mm"
include "3imp.mm"

theorem usgredg2vtxeuALT
  let vy: setvar y
  let cE: class E
  let cG: class G
  let cY: class Y
  let vx: setvar x

  disjoint E y
  disjoint G y
  disjoint Y y
  disjoint E x
  disjoint x y
  disjoint G x
  disjoint Y x
  assert |- ( ( G e. USGraph /\ E e. ( Edg ` G ) /\ Y e. E ) -> E! y e. ( Vtx ` G ) E = { Y , y } )

  proof
    cG
    cusgr
    wcel
    #
    cE
    cG
    cedg
    cfv
    wcel
    #
    cY
    cE
    wcel
    #
    cE
    cY
    vy
    cv
    cpr
    #
    wceq
    #
    vy
    cG
    cvtx
    cfv
    #
    wreu
    #
    @0
    @1
    cE
    vx
    cv
    #
    cG
    ciedg
    cfv
    #
    cfv
    #
    wceq
    #
    vx
    @8
    cdm
    #
    wrex
    #
    @2
    @6
    wi
    #
    @0
    cG
    cuhgr
    wcel
    @1
    @12
    wb
    cG
    usgruhgr
    vx
    cE
    cG
    @8
    @8
    eqid
    #
    uhgredgiedgb
    syl
    @0
    @10
    @13
    vx
    @11
    @0
    @7
    @11
    wcel
    #
    @10
    @13
    @0
    @15
    @10
    w3a
    @13
    cY
    @9
    wcel
    #
    @9
    @3
    wceq
    #
    vy
    @5
    wreu
    #
    wi
    #
    @0
    @15
    @19
    @10
    @0
    @15
    @16
    @18
    vy
    @8
    cG
    @5
    @7
    cY
    @5
    eqid
    @14
    usgredgreu
    3expia
    3adant3
    @10
    @0
    @13
    @19
    wb
    @15
    @10
    @2
    @16
    @6
    @18
    cE
    @9
    cY
    eleq2
    @10
    @4
    @17
    vy
    @5
    cE
    @9
    @3
    eqeq1
    reubidv
    imbi12d
    3ad2ant3
    mpbird
    3exp
    rexlimdv
    sylbid
    3imp
end
