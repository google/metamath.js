include "wss.mm"
include "cxp.mm"
include "cin.mm"
include "cple.mm"
include "cfv.mm"
include "wceq.mm"
include "cpreset.mm"
include "wcel.mm"
include "ineq1i.mm"
include "inass.mm"
include "eqtri.mm"
include "xpss12.mm"
include "anidms.mm"
include "sseqin2.mm"
include "sylib.mm"
include "ineq2d.mm"
include "syl5eq.mm"
include "adantl.mm"

theorem prsss
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let vx: setvar x
  let vy: setvar y
  assume ordtNEW.b: |- B = ( Base ` K )
  assume ordtNEW.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )


  assert |- ( ( K e. Preset /\ A C_ B ) -> ( .<_ i^i ( A X. A ) ) = ( ( le ` K ) i^i ( A X. A ) ) )

  proof
    cA
    cB
    wss
    #
    c.le
    cA
    cA
    cxp
    #
    cin
    #
    cK
    cple
    cfv
    #
    @1
    cin
    #
    wceq
    cK
    cpreset
    wcel
    @0
    @2
    @3
    cB
    cB
    cxp
    #
    @1
    cin
    #
    cin
    #
    @4
    @2
    @3
    @5
    cin
    #
    @1
    cin
    @7
    c.le
    @8
    @1
    ordtNEW.l
    ineq1i
    @3
    @5
    @1
    inass
    eqtri
    @0
    @6
    @1
    @3
    @0
    @1
    @5
    wss
    #
    @6
    @1
    wceq
    @0
    @9
    cA
    cB
    cA
    cB
    xpss12
    anidms
    @1
    @5
    sseqin2
    sylib
    ineq2d
    syl5eq
    adantl
end
