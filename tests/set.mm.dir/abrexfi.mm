include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "rnmpt.mm"
include "mptfi.mm"
include "rnfi.mm"
include "syl.mm"
include "syl5eqelr.mm"

theorem abrexfi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( A e. Fin -> { y | E. x e. A y = B } e. Fin )

  proof
    cA
    cfn
    wcel
    #
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cfn
    vx
    vy
    cA
    cB
    @1
    @1
    eqid
    rnmpt
    @0
    @1
    cfn
    wcel
    @2
    cfn
    wcel
    vx
    cA
    cB
    mptfi
    @1
    rnfi
    syl
    syl5eqelr
end
