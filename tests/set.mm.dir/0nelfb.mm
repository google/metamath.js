include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wnel.mm"
include "wn.mm"
include "cpw.mm"
include "wss.mm"
include "wne.mm"
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
include "simpr2.mm"
include "df-nel.mm"
include "sylib.mm"

theorem 0nelfb
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( F e. ( fBas ` B ) -> -. (/) e. F )

  proof
    cF
    cB
    cfbas
    cfv
    wcel
    #
    c0
    cF
    wnel
    #
    c0
    cF
    wcel
    wn
    @0
    cF
    cB
    cpw
    wss
    #
    cF
    c0
    wne
    #
    @1
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
    @1
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
    @2
    @3
    @1
    @4
    simpr2
    syl
    c0
    cF
    df-nel
    sylib
end
