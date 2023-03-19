include "c0.mm"
include "wf.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cword.mm"
include "wcel.mm"
include "fzo0.mm"
include "eqcomi.mm"
include "feq2i.mm"
include "iswrdi.mm"
include "sylbi.mm"

theorem iswrddm0
  let cS: class S
  let cW: class W


  assert |- ( W : (/) --> S -> W e. Word S )

  proof
    c0
    cS
    cW
    wf
    cc0
    cc0
    cfzo
    co
    #
    cS
    cW
    wf
    cW
    cS
    cword
    wcel
    c0
    @0
    cS
    cW
    @0
    c0
    cc0
    fzo0
    eqcomi
    feq2i
    cS
    cc0
    cW
    iswrdi
    sylbi
end
