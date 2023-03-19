include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "cfn.mm"
include "cint.mm"
include "c0.mm"
include "wne.mm"
include "filfbas.mm"
include "fbfinnfr.mm"
include "syl3an1.mm"

theorem filfinnfr
  let cS: class S
  let cF: class F
  let cX: class X


  assert |- ( ( F e. ( Fil ` X ) /\ S e. F /\ S e. Fin ) -> |^| F =/= (/) )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    cF
    cX
    cfbas
    cfv
    wcel
    cS
    cF
    wcel
    cS
    cfn
    wcel
    cF
    cint
    c0
    wne
    cF
    cX
    filfbas
    cX
    cS
    cF
    fbfinnfr
    syl3an1
end
