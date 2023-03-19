include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfg.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "cfbas.mm"
include "wb.mm"
include "filfbas.mm"
include "elfg.mm"
include "syl.mm"
include "wi.mm"
include "filss.mm"
include "3exp2.mm"
include "com34.mm"
include "rexlimdv.mm"
include "com23.mm"
include "impd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "ssfg.mm"
include "eqssd.mm"

theorem fgfil
  let cF: class F
  let cX: class X
  let vt: setvar t
  let vx: setvar x
  let cA: class A


  assert |- ( F e. ( Fil ` X ) -> ( X filGen F ) = F )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    #
    cX
    cF
    cfg
    co
    #
    cF
    @0
    vt
    @1
    cF
    @0
    vt
    cv
    #
    @1
    wcel
    #
    @2
    cX
    wss
    #
    vx
    cv
    #
    @2
    wss
    #
    vx
    cF
    wrex
    #
    wa
    #
    @2
    cF
    wcel
    #
    @0
    cF
    cX
    cfbas
    cfv
    wcel
    #
    @3
    @8
    wb
    cF
    cX
    filfbas
    #
    vx
    @2
    cF
    cX
    elfg
    syl
    @0
    @4
    @7
    @9
    @0
    @7
    @4
    @9
    @0
    @6
    @4
    @9
    wi
    vx
    cF
    @0
    @5
    cF
    wcel
    #
    @4
    @6
    @9
    @0
    @12
    @4
    @6
    @9
    @5
    @2
    cF
    cX
    filss
    3exp2
    com34
    rexlimdv
    com23
    impd
    sylbid
    ssrdv
    @0
    @10
    cF
    @1
    wss
    @11
    cF
    cX
    ssfg
    syl
    eqssd
end
