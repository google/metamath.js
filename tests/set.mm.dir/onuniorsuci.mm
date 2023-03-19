include "word.mm"
include "cuni.mm"
include "wceq.mm"
include "csuc.mm"
include "wo.mm"
include "onordi.mm"
include "orduniorsuc.mm"
include "ax-mp.mm"

theorem onuniorsuci
  let cA: class A
  assume onssi.1: |- A e. On


  assert |- ( A = U. A \/ A = suc U. A )

  proof
    cA
    word
    cA
    cA
    cuni
    #
    wceq
    cA
    @0
    csuc
    wceq
    wo
    cA
    onssi.1
    onordi
    cA
    orduniorsuc
    ax-mp
end
