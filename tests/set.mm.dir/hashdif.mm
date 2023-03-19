include "cfn.mm"
include "wcel.mm"
include "cdif.mm"
include "chash.mm"
include "cfv.mm"
include "cin.mm"
include "cmin.mm"
include "co.mm"
include "difin.mm"
include "fveq2i.mm"
include "wss.mm"
include "wceq.mm"
include "inss1.mm"
include "hashssdif.mm"
include "mpan2.mm"
include "syl5eqr.mm"

theorem hashdif
  let cA: class A
  let cB: class B


  assert |- ( A e. Fin -> ( # ` ( A \ B ) ) = ( ( # ` A ) - ( # ` ( A i^i B ) ) ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    cB
    cdif
    #
    chash
    cfv
    cA
    cA
    cB
    cin
    #
    cdif
    #
    chash
    cfv
    #
    cA
    chash
    cfv
    @2
    chash
    cfv
    cmin
    co
    #
    @3
    @1
    chash
    cA
    cB
    difin
    fveq2i
    @0
    @2
    cA
    wss
    @4
    @5
    wceq
    cA
    cB
    inss1
    cA
    @2
    hashssdif
    mpan2
    syl5eqr
end
