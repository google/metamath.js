include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "w3a.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
include "wceq.mm"
include "wa.mm"
include "1z.mm"
include "expsub.mm"
include "mpanr2.mm"
include "3impa.mm"
include "exp1.mm"
include "3ad2ant1.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem expm1
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. ZZ ) -> ( A ^ ( N - 1 ) ) = ( ( A ^ N ) / A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cA
    cN
    c1
    cmin
    co
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cA
    c1
    cexp
    co
    #
    cdiv
    co
    #
    @5
    cA
    cdiv
    co
    @0
    @1
    @2
    @4
    @7
    wceq
    #
    @0
    @1
    wa
    @2
    c1
    cz
    wcel
    @8
    1z
    cA
    cN
    c1
    expsub
    mpanr2
    3impa
    @3
    @6
    cA
    @5
    cdiv
    @0
    @1
    @6
    cA
    wceq
    @2
    cA
    exp1
    3ad2ant1
    oveq2d
    eqtrd
end
