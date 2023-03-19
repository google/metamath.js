include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "ciun.mm"
include "wceq.mm"
include "iunxsngf2.mm"
include "ax-mp.mm"

theorem iunxsnf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iunxsnf.1: |- F/_ x C
  assume iunxsnf.2: |- A e. _V
  assume iunxsnf.3: |- ( x = A -> B = C )

  disjoint A x
  assert |- U_ x e. { A } B = C

  proof
    cA
    cvv
    wcel
    vx
    cA
    csn
    cB
    ciun
    cC
    wceq
    iunxsnf.2
    vx
    cA
    cB
    cC
    cvv
    iunxsnf.1
    iunxsnf.3
    iunxsngf2
    ax-mp
end
