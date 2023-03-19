include "ct0.mm"
include "wcel.mm"
include "ckq.mm"
include "cfv.mm"
include "chmph.mm"
include "wbr.mm"
include "cuni.mm"
include "wel.mm"
include "crab.mm"
include "cmpt.mm"
include "chmeo.mm"
include "co.mm"
include "ctopon.mm"
include "wb.mm"
include "ctop.mm"
include "t0top.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "t0kq.mm"
include "syl.mm"
include "ibi.mm"
include "hmphi.mm"
include "hmphsym.mm"
include "hmphtop1.mm"
include "kqt0.mm"
include "t0hmph.mm"
include "sylc.mm"
include "impbii.mm"

theorem kqhmph
  let cJ: class J
  let vx: setvar x
  let vy: setvar y


  assert |- ( J e. Kol2 <-> J ~= ( KQ ` J ) )

  proof
    cJ
    ct0
    wcel
    #
    cJ
    cJ
    ckq
    cfv
    #
    chmph
    wbr
    #
    @0
    vx
    cJ
    cuni
    #
    vx
    vy
    wel
    vy
    cJ
    crab
    cmpt
    #
    cJ
    @1
    chmeo
    co
    wcel
    #
    @2
    @0
    @5
    @0
    cJ
    @3
    ctopon
    cfv
    wcel
    #
    @0
    @5
    wb
    @0
    cJ
    ctop
    wcel
    #
    @6
    cJ
    t0top
    cJ
    @3
    @3
    eqid
    toptopon
    sylib
    vx
    vy
    @4
    cJ
    @3
    @4
    eqid
    t0kq
    syl
    ibi
    @4
    cJ
    @1
    hmphi
    syl
    @2
    @1
    cJ
    chmph
    wbr
    @1
    ct0
    wcel
    #
    @0
    cJ
    @1
    hmphsym
    @2
    @7
    @8
    cJ
    @1
    hmphtop1
    cJ
    kqt0
    sylib
    @1
    cJ
    t0hmph
    sylc
    impbii
end
