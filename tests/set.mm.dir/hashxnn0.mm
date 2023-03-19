include "wcel.mm"
include "cvv.mm"
include "cxnn0.mm"
include "chash.mm"
include "wf.mm"
include "hashfxnn0.mm"
include "a1i.mm"
include "elex.mm"
include "ffvelrnd.mm"

theorem hashxnn0
  let cM: class M
  let cV: class V


  assert |- ( M e. V -> ( # ` M ) e. NN0* )

  proof
    cM
    cV
    wcel
    #
    cvv
    cxnn0
    cM
    chash
    cvv
    cxnn0
    chash
    wf
    @0
    hashfxnn0
    a1i
    cM
    cV
    elex
    ffvelrnd
end
