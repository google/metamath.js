include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfg.mm"
include "co.mm"
include "cv.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "ssrexv.mm"
include "anim2d.mm"
include "3ad2ant3.mm"
include "wb.mm"
include "elfg.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem fgss
  let cF: class F
  let cG: class G
  let cX: class X
  let vt: setvar t
  let vx: setvar x


  assert |- ( ( F e. ( fBas ` X ) /\ G e. ( fBas ` X ) /\ F C_ G ) -> ( X filGen F ) C_ ( X filGen G ) )

  proof
    cF
    cX
    cfbas
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    cF
    cG
    wss
    #
    w3a
    #
    vt
    cX
    cF
    cfg
    co
    #
    cX
    cG
    cfg
    co
    #
    @4
    vt
    cv
    #
    cX
    wss
    #
    vx
    cv
    @7
    wss
    #
    vx
    cF
    wrex
    #
    wa
    #
    @8
    @9
    vx
    cG
    wrex
    #
    wa
    #
    @7
    @5
    wcel
    #
    @7
    @6
    wcel
    #
    @3
    @1
    @11
    @13
    wi
    @2
    @3
    @10
    @12
    @8
    @9
    vx
    cF
    cG
    ssrexv
    anim2d
    3ad2ant3
    @1
    @2
    @14
    @11
    wb
    @3
    vx
    @7
    cF
    cX
    elfg
    3ad2ant1
    @2
    @1
    @15
    @13
    wb
    @3
    vx
    @7
    cG
    cX
    elfg
    3ad2ant2
    3imtr4d
    ssrdv
end
