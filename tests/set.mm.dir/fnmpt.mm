include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "wfn.mm"
include "elex.mm"
include "ralimi.mm"
include "mptfng.mm"
include "sylib.mm"

theorem fnmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vy: setvar y
  assume mptfng.1: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A. x e. A B e. V -> F Fn A )

  proof
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    cF
    cA
    wfn
    @0
    @1
    vx
    cA
    cB
    cV
    elex
    ralimi
    vx
    cA
    cB
    cF
    mptfng.1
    mptfng
    sylib
end
