include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "cjcj.mm"
include "eqeqan12d.mm"
include "syl5ib.mm"
include "impbid1.mm"

theorem cj11
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( * ` A ) = ( * ` B ) <-> A = B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    ccj
    cfv
    #
    cB
    ccj
    cfv
    #
    wceq
    #
    cA
    cB
    wceq
    #
    @5
    @3
    ccj
    cfv
    #
    @4
    ccj
    cfv
    #
    wceq
    @2
    @6
    @3
    @4
    ccj
    fveq2
    @0
    @1
    @7
    cA
    @8
    cB
    cA
    cjcj
    cB
    cjcj
    eqeqan12d
    syl5ib
    cA
    cB
    ccj
    fveq2
    impbid1
end
