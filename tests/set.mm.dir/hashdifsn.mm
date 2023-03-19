include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "wss.mm"
include "wceq.mm"
include "snssi.mm"
include "hashssdif.mm"
include "sylan2.mm"
include "hashsng.mm"
include "adantl.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem hashdifsn
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Fin /\ B e. A ) -> ( # ` ( A \ { B } ) ) = ( ( # ` A ) - 1 ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cA
    wcel
    #
    wa
    #
    cA
    cB
    csn
    #
    cdif
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    @3
    chash
    cfv
    #
    cmin
    co
    #
    @5
    c1
    cmin
    co
    @1
    @0
    @3
    cA
    wss
    @4
    @7
    wceq
    cB
    cA
    snssi
    cA
    @3
    hashssdif
    sylan2
    @2
    @6
    c1
    @5
    cmin
    @1
    @6
    c1
    wceq
    @0
    cB
    cA
    hashsng
    adantl
    oveq2d
    eqtrd
end
