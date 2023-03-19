include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "cfv.mm"
include "wceq.mm"
include "snidg.mm"
include "fvres.mm"
include "syl.mm"

theorem fvressn
  let cF: class F
  let cV: class V
  let cX: class X


  assert |- ( X e. V -> ( ( F |` { X } ) ` X ) = ( F ` X ) )

  proof
    cX
    cV
    wcel
    cX
    cX
    csn
    #
    wcel
    cX
    cF
    @0
    cres
    cfv
    cX
    cF
    cfv
    wceq
    cX
    cV
    snidg
    cX
    @0
    cF
    fvres
    syl
end
