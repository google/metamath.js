include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cfv.mm"
include "eqid.mm"
include "cv.mm"
include "eqeq2d.mm"
include "eqeq1.mm"
include "wmo.mm"
include "moeq.mm"
include "a1i.mm"
include "cmpt.mm"
include "copab.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "fvopab3ig.mm"
include "mpi.mm"

theorem fvmptg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let vy: setvar y
  assume fvmptg.1: |- ( x = A -> B = C )
  assume fvmptg.2: |- F = ( x e. D |-> B )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  assert |- ( ( A e. D /\ C e. R ) -> ( F ` A ) = C )

  proof
    cA
    cD
    wcel
    cC
    cR
    wcel
    wa
    cC
    cC
    wceq
    #
    cA
    cF
    cfv
    cC
    wceq
    cC
    eqid
    vy
    cv
    #
    cB
    wceq
    #
    @1
    cC
    wceq
    @0
    vx
    vy
    cA
    cC
    cD
    cR
    cF
    vx
    cv
    #
    cA
    wceq
    cB
    cC
    @1
    fvmptg.1
    eqeq2d
    @1
    cC
    cC
    eqeq1
    @2
    vy
    wmo
    @3
    cD
    wcel
    #
    vy
    cB
    moeq
    a1i
    cF
    vx
    cD
    cB
    cmpt
    @4
    @2
    wa
    vx
    vy
    copab
    fvmptg.2
    vx
    vy
    cD
    cB
    df-mpt
    eqtri
    fvopab3ig
    mpi
end
