include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cfv.mm"
include "fvres.mm"
include "fvi.mm"
include "eqtrd.mm"

theorem fvresi
  let cA: class A
  let cB: class B


  assert |- ( B e. A -> ( ( _I |` A ) ` B ) = B )

  proof
    cB
    cA
    wcel
    cB
    cid
    cA
    cres
    cfv
    cB
    cid
    cfv
    cB
    cB
    cA
    cid
    fvres
    cB
    cA
    fvi
    eqtrd
end
