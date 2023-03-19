include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "simp2.mm"
include "wa.mm"
include "simp1.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "3ad2ant1.mm"
include "isfbas.mm"
include "syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "3ad2ant3.mm"
include "mpbir2and.mm"

theorem fbasweak
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. ( fBas ` X ) /\ F C_ ~P Y /\ Y e. V ) -> F e. ( fBas ` Y ) )

  proof
    cF
    cX
    cfbas
    cfv
    wcel
    #
    cF
    cY
    cpw
    wss
    #
    cY
    cV
    wcel
    #
    w3a
    #
    cF
    cY
    cfbas
    cfv
    wcel
    #
    @1
    cF
    c0
    wne
    c0
    cF
    wnel
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
    w3a
    #
    @0
    @1
    @2
    simp2
    @3
    cF
    cX
    cpw
    wss
    #
    @5
    @3
    @0
    @6
    @5
    wa
    #
    @0
    @1
    @2
    simp1
    @3
    cX
    cfbas
    cdm
    #
    wcel
    #
    @0
    @7
    wb
    @0
    @1
    @9
    @2
    cF
    cX
    cfbas
    elfvdm
    3ad2ant1
    vx
    vy
    @8
    cX
    cF
    isfbas
    syl
    mpbid
    simprd
    @2
    @0
    @4
    @1
    @5
    wa
    wb
    @1
    vx
    vy
    cV
    cY
    cF
    isfbas
    3ad2ant3
    mpbir2and
end
