include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "nnz.mm"
include "gcdcom.mm"
include "sylan.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "divgcdnn.mm"
include "eqeltrd.mm"

theorem divgcdnnr
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. ZZ ) -> ( A / ( B gcd A ) ) e. NN )

  proof
    cA
    cn
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cA
    cgcd
    co
    #
    cdiv
    co
    cA
    cA
    cB
    cgcd
    co
    #
    cdiv
    co
    cn
    @2
    @3
    @4
    cA
    cdiv
    @2
    @4
    @3
    @0
    cA
    cz
    wcel
    @1
    @4
    @3
    wceq
    cA
    nnz
    cA
    cB
    gcdcom
    sylan
    eqcomd
    oveq2d
    cA
    cB
    divgcdnn
    eqeltrd
end
