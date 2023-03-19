include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "wfn.mm"
include "rgenw.mm"
include "mptfng.mm"
include "mpbi.mm"

theorem fnmpti
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume fnmpti.1: |- B e. _V
  assume fnmpti.2: |- F = ( x e. A |-> B )

  disjoint A x
  assert |- F Fn A

  proof
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
    vx
    cA
    fnmpti.1
    rgenw
    vx
    cA
    cB
    cF
    fnmpti.2
    mptfng
    mpbi
end
