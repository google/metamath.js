include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "ciun.mm"
include "wceq.mm"
include "iunxsng.mm"
include "ax-mp.mm"

theorem iunxsn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iunxsn.1: |- A e. _V
  assume iunxsn.2: |- ( x = A -> B = C )

  disjoint A x
  disjoint C x
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
    iunxsn.1
    vx
    cA
    cB
    cC
    cvv
    iunxsn.2
    iunxsng
    ax-mp
end
