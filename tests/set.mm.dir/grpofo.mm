include "cgr.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "wfo.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "isgrpo.mm"
include "ibi.mm"
include "simp1d.mm"
include "eqcomi.mm"
include "jctir.mm"
include "dffo2.mm"
include "sylibr.mm"

theorem grpofo
  let cG: class G
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vu: setvar u
  let cU: class U
  assume grpfo.1: |- X = ran G


  assert |- ( G e. GrpOp -> G : ( X X. X ) -onto-> X )

  proof
    cG
    cgr
    wcel
    #
    cX
    cX
    cxp
    #
    cX
    cG
    wf
    #
    cG
    crn
    #
    cX
    wceq
    #
    wa
    @1
    cX
    cG
    wfo
    @0
    @2
    @4
    @0
    @2
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    vz
    cv
    #
    cG
    co
    @5
    @6
    @7
    cG
    co
    cG
    co
    wceq
    vz
    cX
    wral
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vu
    cv
    #
    @5
    cG
    co
    @5
    wceq
    @6
    @5
    cG
    co
    @9
    wceq
    vy
    cX
    wrex
    wa
    vx
    cX
    wral
    vu
    cX
    wrex
    #
    @0
    @2
    @8
    @10
    w3a
    vx
    vy
    vz
    vu
    cgr
    cG
    cX
    grpfo.1
    isgrpo
    ibi
    simp1d
    cX
    @3
    grpfo.1
    eqcomi
    jctir
    @1
    cX
    cG
    dffo2
    sylibr
end
