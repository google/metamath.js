include "wss.mm"
include "ctg.mm"
include "cfv.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "ssex.mm"
include "adantl.mm"
include "simpl.mm"
include "tgss.mm"
include "syl2anc.mm"
include "simpr.mm"
include "wb.mm"
include "ssexg.mm"
include "sylan2.mm"
include "tgss3.mm"
include "mpbird.mm"
include "eqssd.mm"

theorem 2basgen
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cV: class V


  assert |- ( ( B C_ C /\ C C_ ( topGen ` B ) ) -> ( topGen ` B ) = ( topGen ` C ) )

  proof
    cB
    cC
    wss
    #
    cC
    cB
    ctg
    cfv
    #
    wss
    #
    wa
    #
    @1
    cC
    ctg
    cfv
    #
    @3
    cC
    cvv
    wcel
    #
    @0
    @1
    @4
    wss
    @2
    @5
    @0
    cC
    @1
    cB
    ctg
    fvex
    ssex
    #
    adantl
    #
    @0
    @2
    simpl
    cB
    cC
    cvv
    tgss
    syl2anc
    @3
    @4
    @1
    wss
    #
    @2
    @0
    @2
    simpr
    @3
    @5
    cB
    cvv
    wcel
    #
    @8
    @2
    wb
    @7
    @2
    @0
    @5
    @9
    @6
    cB
    cC
    cvv
    ssexg
    sylan2
    cC
    cB
    cvv
    cvv
    tgss3
    syl2anc
    mpbird
    eqssd
end
