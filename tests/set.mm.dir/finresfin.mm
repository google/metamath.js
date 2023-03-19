include "cfn.mm"
include "wcel.mm"
include "cres.mm"
include "wss.mm"
include "resss.mm"
include "ssfi.mm"
include "mpan2.mm"

theorem finresfin
  let cB: class B
  let cE: class E


  assert |- ( E e. Fin -> ( E |` B ) e. Fin )

  proof
    cE
    cfn
    wcel
    cE
    cB
    cres
    #
    cE
    wss
    @0
    cfn
    wcel
    cE
    cB
    resss
    cE
    @0
    ssfi
    mpan2
end
