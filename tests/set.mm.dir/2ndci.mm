include "ctb.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "c2ndc.mm"
include "simpl.mm"
include "simpr.mm"
include "eqidd.mm"
include "breq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "is2ndc.mm"
include "sylibr.mm"

theorem 2ndci
  let cB: class B
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cJ: class J


  assert |- ( ( B e. TopBases /\ B ~<_ _om ) -> ( topGen ` B ) e. 2ndc )

  proof
    cB
    ctb
    wcel
    #
    cB
    com
    cdom
    wbr
    #
    wa
    #
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @3
    ctg
    cfv
    #
    cB
    ctg
    cfv
    #
    wceq
    #
    wa
    #
    vx
    ctb
    wrex
    #
    @6
    c2ndc
    wcel
    @2
    @0
    @1
    @6
    @6
    wceq
    #
    @9
    @0
    @1
    simpl
    @0
    @1
    simpr
    @2
    @6
    eqidd
    @8
    @1
    @10
    wa
    vx
    cB
    ctb
    @3
    cB
    wceq
    #
    @4
    @1
    @7
    @10
    @3
    cB
    com
    cdom
    breq1
    @11
    @5
    @6
    @6
    @3
    cB
    ctg
    fveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    vx
    @6
    is2ndc
    sylibr
end
