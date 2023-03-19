include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "isfbas.mm"
include "syl.mm"
include "ibi.mm"
include "simpr1.mm"

theorem fbasne0
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( F e. ( fBas ` B ) -> F =/= (/) )

  proof
    cF
    cB
    cfbas
    cfv
    wcel
    #
    cF
    cB
    cpw
    wss
    #
    cF
    c0
    wne
    #
    c0
    cF
    wnel
    #
    cF
    vx
    cv
    vy
    cv
    cin
    cpw
    cin
    c0
    wne
    vy
    cF
    wral
    vx
    cF
    wral
    #
    w3a
    wa
    #
    @2
    @0
    @5
    @0
    cB
    cfbas
    cdm
    #
    wcel
    @0
    @5
    wb
    cF
    cB
    cfbas
    elfvdm
    vx
    vy
    @6
    cB
    cF
    isfbas
    syl
    ibi
    @1
    @2
    @3
    @4
    simpr1
    syl
end
