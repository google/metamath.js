include "wss.mm"
include "ccref.mm"
include "cv.mm"
include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "cref.mm"
include "wbr.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "sslin.mm"
include "ssrexv.mm"
include "syl.mm"
include "imim2d.mm"
include "ralimdv.mm"
include "anim2d.mm"
include "eqid.mm"
include "iscref.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem crefss
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vy: setvar y
  let vz: setvar z


  assert |- ( A C_ B -> CovHasRef A C_ CovHasRef B )

  proof
    cA
    cB
    wss
    #
    vj
    cA
    ccref
    #
    cB
    ccref
    #
    @0
    vj
    cv
    #
    ctop
    wcel
    #
    @3
    cuni
    #
    vy
    cv
    #
    cuni
    wceq
    #
    vz
    cv
    @6
    cref
    wbr
    #
    vz
    @3
    cpw
    #
    cA
    cin
    #
    wrex
    #
    wi
    #
    vy
    @9
    wral
    #
    wa
    @4
    @7
    @8
    vz
    @9
    cB
    cin
    #
    wrex
    #
    wi
    #
    vy
    @9
    wral
    #
    wa
    @3
    @1
    wcel
    @3
    @2
    wcel
    @0
    @13
    @17
    @4
    @0
    @12
    @16
    vy
    @9
    @0
    @11
    @15
    @7
    @0
    @10
    @14
    wss
    @11
    @15
    wi
    cA
    cB
    @9
    sslin
    @8
    vz
    @10
    @14
    ssrexv
    syl
    imim2d
    ralimdv
    anim2d
    vy
    vz
    cA
    @3
    @5
    @5
    eqid
    #
    iscref
    vy
    vz
    cB
    @3
    @5
    @18
    iscref
    3imtr4g
    ssrdv
end
