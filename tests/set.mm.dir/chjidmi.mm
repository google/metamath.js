include "cch.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "chjidm.mm"
include "ax-mp.mm"

theorem chjidmi
  let cA: class A
  assume chjidm.1: |- A e. CH


  assert |- ( A vH A ) = A

  proof
    cA
    cch
    wcel
    cA
    cA
    chj
    co
    cA
    wceq
    chjidm.1
    cA
    chjidm
    ax-mp
end
