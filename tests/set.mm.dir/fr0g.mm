include "wcel.mm"
include "c0.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "cfv.mm"
include "wceq.mm"
include "peano1.mm"
include "fvres.mm"
include "ax-mp.mm"
include "rdg0g.mm"
include "syl5eq.mm"

theorem fr0g
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( A e. B -> ( ( rec ( F , A ) |` _om ) ` (/) ) = A )

  proof
    cA
    cB
    wcel
    c0
    cF
    cA
    crdg
    #
    com
    cres
    cfv
    #
    c0
    @0
    cfv
    #
    cA
    c0
    com
    wcel
    @1
    @2
    wceq
    peano1
    c0
    com
    @0
    fvres
    ax-mp
    cA
    cB
    cF
    rdg0g
    syl5eq
end
