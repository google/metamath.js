include "wcel.mm"
include "wn.mm"
include "wo.mm"
include "cres.mm"
include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "exmid.mm"
include "fvres.mm"
include "nfvres.mm"
include "orim12i.mm"
include "ax-mp.mm"

theorem fvresval
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( ( F |` B ) ` A ) = ( F ` A ) \/ ( ( F |` B ) ` A ) = (/) )

  proof
    cA
    cB
    wcel
    #
    @0
    wn
    #
    wo
    cA
    cF
    cB
    cres
    cfv
    #
    cA
    cF
    cfv
    wceq
    #
    @2
    c0
    wceq
    #
    wo
    @0
    exmid
    @0
    @3
    @1
    @4
    cA
    cB
    cF
    fvres
    cA
    cB
    cF
    nfvres
    orim12i
    ax-mp
end
