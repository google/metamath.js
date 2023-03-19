include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wa.mm"
include "wss.mm"
include "cfg.mm"
include "co.mm"
include "cv.mm"
include "wrex.mm"
include "wb.mm"
include "elfg.mm"
include "adantr.mm"
include "wi.mm"
include "ssrexv.mm"
include "adantl.mm"
include "filss.mm"
include "3exp2.mm"
include "com34.mm"
include "rexlimdv.mm"
include "ad2antlr.mm"
include "syld.mm"
include "com23.mm"
include "impd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "ex.mm"
include "ssfg.mm"
include "sstr2.mm"
include "syl.mm"
include "impbid.mm"

theorem fgmin
  let cB: class B
  let cF: class F
  let cX: class X
  let vt: setvar t
  let vx: setvar x


  assert |- ( ( B e. ( fBas ` X ) /\ F e. ( Fil ` X ) ) -> ( B C_ F <-> ( X filGen B ) C_ F ) )

  proof
    cB
    cX
    cfbas
    cfv
    wcel
    #
    cF
    cX
    cfil
    cfv
    wcel
    #
    wa
    #
    cB
    cF
    wss
    #
    cX
    cB
    cfg
    co
    #
    cF
    wss
    #
    @2
    @3
    @5
    @2
    @3
    wa
    #
    vt
    @4
    cF
    @6
    vt
    cv
    #
    @4
    wcel
    #
    @7
    cX
    wss
    #
    vx
    cv
    #
    @7
    wss
    #
    vx
    cB
    wrex
    #
    wa
    #
    @7
    cF
    wcel
    #
    @2
    @8
    @13
    wb
    #
    @3
    @0
    @15
    @1
    vx
    @7
    cB
    cX
    elfg
    adantr
    adantr
    @6
    @9
    @12
    @14
    @6
    @12
    @9
    @14
    @6
    @12
    @11
    vx
    cF
    wrex
    #
    @9
    @14
    wi
    #
    @3
    @12
    @16
    wi
    @2
    @11
    vx
    cB
    cF
    ssrexv
    adantl
    @1
    @16
    @17
    wi
    @0
    @3
    @1
    @11
    @17
    vx
    cF
    @1
    @10
    cF
    wcel
    #
    @9
    @11
    @14
    @1
    @18
    @9
    @11
    @14
    @10
    @7
    cF
    cX
    filss
    3exp2
    com34
    rexlimdv
    ad2antlr
    syld
    com23
    impd
    sylbid
    ssrdv
    ex
    @0
    @5
    @3
    wi
    #
    @1
    @0
    cB
    @4
    wss
    @19
    cB
    cX
    ssfg
    cB
    @4
    cF
    sstr2
    syl
    adantr
    impbid
end
