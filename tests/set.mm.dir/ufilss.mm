include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cdif.mm"
include "wo.mm"
include "cpw.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "elpw2g.mm"
include "syl.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "cfil.mm"
include "isufil.mm"
include "simprbi.mm"
include "wceq.mm"
include "eleq1.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "orbi12d.mm"
include "rspccv.mm"
include "sylbird.mm"
include "imp.mm"

theorem ufilss
  let cS: class S
  let cF: class F
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cG: class G


  assert |- ( ( F e. ( UFil ` X ) /\ S C_ X ) -> ( S e. F \/ ( X \ S ) e. F ) )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    cS
    cF
    wcel
    #
    cX
    cS
    cdif
    #
    cF
    wcel
    #
    wo
    #
    @0
    @1
    cS
    cX
    cpw
    #
    wcel
    #
    @5
    @0
    cX
    cufil
    cdm
    #
    wcel
    @7
    @1
    wb
    cF
    cX
    cufil
    elfvdm
    cS
    cX
    @8
    elpw2g
    syl
    @0
    vx
    cv
    #
    cF
    wcel
    #
    cX
    @9
    cdif
    #
    cF
    wcel
    #
    wo
    #
    vx
    @6
    wral
    #
    @7
    @5
    wi
    @0
    cF
    cX
    cfil
    cfv
    wcel
    @14
    vx
    cF
    cX
    isufil
    simprbi
    @13
    @5
    vx
    cS
    @6
    @9
    cS
    wceq
    #
    @10
    @2
    @12
    @4
    @9
    cS
    cF
    eleq1
    @15
    @11
    @3
    cF
    @9
    cS
    cX
    difeq2
    eleq1d
    orbi12d
    rspccv
    syl
    sylbird
    imp
end
