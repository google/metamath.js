include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "co.mm"
include "cconcat.mm"
include "wceq.mm"
include "wa.mm"
include "cn.mm"
include "cn0.mm"
include "lencl.mm"
include "elnnnn0b.mm"
include "biimpri.mm"
include "sylan.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "3adant2.mm"
include "ccatval1.mm"
include "syld3an3.mm"

theorem ccatfv0
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. Word V /\ B e. Word V /\ 0 < ( # ` A ) ) -> ( ( A ++ B ) ` 0 ) = ( A ` 0 ) )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cc0
    cA
    chash
    cfv
    #
    clt
    wbr
    #
    cc0
    cc0
    @3
    cfzo
    co
    wcel
    #
    cc0
    cA
    cB
    cconcat
    co
    cfv
    cc0
    cA
    cfv
    wceq
    @1
    @4
    @5
    @2
    @1
    @4
    wa
    @3
    cn
    wcel
    #
    @5
    @1
    @3
    cn0
    wcel
    #
    @4
    @6
    cV
    cA
    lencl
    @6
    @7
    @4
    wa
    @3
    elnnnn0b
    biimpri
    sylan
    @3
    lbfzo0
    sylibr
    3adant2
    cV
    cA
    cB
    cc0
    ccatval1
    syld3an3
end
