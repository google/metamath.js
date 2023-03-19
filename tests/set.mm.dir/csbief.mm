include "cvv.mm"
include "wcel.mm"
include "csb.mm"
include "wceq.mm"
include "wnfc.mm"
include "a1i.mm"
include "csbiegf.mm"
include "ax-mp.mm"

theorem csbief
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume csbief.1: |- A e. _V
  assume csbief.2: |- F/_ x C
  assume csbief.3: |- ( x = A -> B = C )

  disjoint A x
  assert |- [_ A / x ]_ B = C

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    cB
    csb
    cC
    wceq
    csbief.1
    vx
    cA
    cB
    cC
    cvv
    vx
    cC
    wnfc
    @0
    csbief.2
    a1i
    csbief.3
    csbiegf
    ax-mp
end
