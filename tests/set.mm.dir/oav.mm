include "con0.mm"
include "cv.mm"
include "cvv.mm"
include "csuc.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "coa.mm"
include "wceq.mm"
include "rdgeq2.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "df-oadd.mm"
include "fvex.mm"
include "ovmpt2.mm"

theorem oav
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
  assert |- ( ( A e. On /\ B e. On ) -> ( A +o B ) = ( rec ( ( x e. _V |-> suc x ) , A ) ` B ) )

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
    csuc
    cmpt
    #
    vy
    cv
    #
    crdg
    #
    cfv
    cB
    @1
    cA
    crdg
    #
    cfv
    coa
    @0
    @4
    cfv
    @2
    cA
    wceq
    @0
    @3
    @4
    @2
    cA
    @1
    rdgeq2
    fveq1d
    @0
    cB
    @4
    fveq2
    vy
    vz
    vx
    df-oadd
    cB
    @4
    fvex
    ovmpt2
end
