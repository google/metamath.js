include "cv.mm"
include "wcel.mm"
include "cpr.mm"
include "wrex.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wne.mm"
include "wa.mm"
include "wi.mm"
include "elss2prb.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "biimpcd.mm"
include "reximdv.mm"
include "com12.mm"
include "sylbi.mm"
include "rexlimiv.mm"

theorem exprelprel
  let vw: setvar w
  let vv: setvar v
  let ve: setvar e
  let cV: class V
  let cX: class X
  let vp: setvar p

  disjoint V e
  disjoint V p
  disjoint V v
  disjoint V w
  disjoint e p
  disjoint e v
  disjoint e w
  disjoint p v
  disjoint p w
  disjoint v w
  disjoint X p
  disjoint X v
  disjoint X w
  assert |- ( E. p e. { e e. ~P V | ( # ` e ) = 2 } p e. X -> E. v e. V E. w e. V { v , w } e. X )

  proof
    vp
    cv
    #
    cX
    wcel
    #
    vv
    cv
    #
    vw
    cv
    #
    cpr
    #
    cX
    wcel
    #
    vw
    cV
    wrex
    #
    vv
    cV
    wrex
    #
    vp
    ve
    cv
    chash
    cfv
    c2
    wceq
    ve
    cV
    cpw
    crab
    #
    @0
    @8
    wcel
    @2
    @3
    wne
    #
    @0
    @4
    wceq
    #
    wa
    #
    vw
    cV
    wrex
    #
    vv
    cV
    wrex
    #
    @1
    @7
    wi
    vv
    vw
    ve
    @0
    cV
    elss2prb
    @1
    @13
    @7
    @1
    @12
    @6
    vv
    cV
    @1
    @11
    @5
    vw
    cV
    @11
    @1
    @5
    @10
    @1
    @5
    wb
    @9
    @0
    @4
    cX
    eleq1
    adantl
    biimpcd
    reximdv
    reximdv
    com12
    sylbi
    rexlimiv
end
