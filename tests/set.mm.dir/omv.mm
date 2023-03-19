include "con0.mm"
include "cv.mm"
include "cvv.mm"
include "coa.mm"
include "co.mm"
include "cmpt.mm"
include "c0.mm"
include "crdg.mm"
include "cfv.mm"
include "comu.mm"
include "wceq.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "rdgeq1.mm"
include "syl.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "df-omul.mm"
include "fvex.mm"
include "ovmpt2.mm"

theorem omv
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( A e. On /\ B e. On ) -> ( A .o B ) = ( rec ( ( x e. _V |-> ( x +o A ) ) , (/) ) ` B ) )

  proof
    vy
    vz
    cA
    cB
    con0
    con0
    vz
    cv
    #
    vx
    cvv
    vx
    cv
    #
    vy
    cv
    #
    coa
    co
    #
    cmpt
    #
    c0
    crdg
    #
    cfv
    cB
    vx
    cvv
    @1
    cA
    coa
    co
    #
    cmpt
    #
    c0
    crdg
    #
    cfv
    comu
    @0
    @8
    cfv
    @2
    cA
    wceq
    #
    @0
    @5
    @8
    @9
    @4
    @7
    wceq
    @5
    @8
    wceq
    @9
    vx
    cvv
    @3
    @6
    @2
    cA
    @1
    coa
    oveq2
    mpteq2dv
    c0
    @4
    @7
    rdgeq1
    syl
    fveq1d
    @0
    cB
    @8
    fveq2
    vy
    vz
    vx
    df-omul
    cB
    @8
    fvex
    ovmpt2
end
