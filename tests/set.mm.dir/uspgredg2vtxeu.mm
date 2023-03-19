include "cuspgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "cvtx.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "eqid.mm"
include "upgredg2vtx.mm"
include "syl3an1.mm"
include "eqtr2.mm"
include "vex.mm"
include "preqr2.mm"
include "syl.mm"
include "a1i.mm"
include "ralrimivva.mm"
include "preq2.mm"
include "eqeq2d.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem uspgredg2vtxeu
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
  assert |- ( ( G e. USPGraph /\ E e. ( Edg ` G ) /\ Y e. E ) -> E! y e. ( Vtx ` G ) E = { Y , y } )

  proof
    cG
    cuspgr
    wcel
    #
    cE
    cG
    cedg
    cfv
    #
    wcel
    #
    cY
    cE
    wcel
    #
    w3a
    #
    cE
    cY
    vy
    cv
    #
    cpr
    #
    wceq
    #
    vy
    cG
    cvtx
    cfv
    #
    wrex
    #
    @7
    cE
    cY
    vx
    cv
    #
    cpr
    #
    wceq
    #
    wa
    #
    vy
    vx
    weq
    #
    wi
    #
    vx
    @8
    wral
    vy
    @8
    wral
    @7
    vy
    @8
    wreu
    @0
    cG
    cupgr
    wcel
    @2
    @3
    @9
    cG
    uspgrupgr
    cY
    cE
    @1
    cG
    @8
    vy
    @8
    eqid
    @1
    eqid
    upgredg2vtx
    syl3an1
    @4
    @15
    vy
    vx
    @8
    @8
    @15
    @4
    @5
    @8
    wcel
    @10
    @8
    wcel
    wa
    wa
    @13
    @6
    @11
    wceq
    @14
    cE
    @6
    @11
    eqtr2
    @5
    @10
    cY
    vy
    vex
    vx
    vex
    preqr2
    syl
    a1i
    ralrimivva
    @7
    @12
    vy
    vx
    @8
    @14
    @6
    @11
    cE
    @5
    @10
    cY
    preq2
    eqeq2d
    reu4
    sylanbrc
end
