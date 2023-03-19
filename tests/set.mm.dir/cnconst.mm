include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "wf.mm"
include "ccn.mm"
include "co.mm"
include "cxp.mm"
include "wceq.mm"
include "wb.mm"
include "fconst2g.mm"
include "adantl.mm"
include "cnconst2.mm"
include "3expa.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "impr.mm"

theorem cnconst
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) /\ ( B e. Y /\ F : X --> { B } ) ) -> F e. ( J Cn K ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    cB
    cY
    wcel
    #
    cX
    cB
    csn
    #
    cF
    wf
    #
    cF
    cJ
    cK
    ccn
    co
    #
    wcel
    #
    @2
    @3
    wa
    #
    @5
    cF
    cX
    @4
    cxp
    #
    wceq
    #
    @7
    @3
    @5
    @10
    wb
    @2
    cX
    cB
    cY
    cF
    fconst2g
    adantl
    @8
    @7
    @10
    @9
    @6
    wcel
    #
    @0
    @1
    @3
    @11
    cB
    cJ
    cK
    cX
    cY
    cnconst2
    3expa
    cF
    @9
    @6
    eleq1
    syl5ibrcom
    sylbid
    impr
end
