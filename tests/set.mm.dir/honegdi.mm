include "c1.mm"
include "cneg.mm"
include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "chos.mm"
include "co.mm"
include "chot.mm"
include "wceq.mm"
include "neg1cn.mm"
include "hoadddi.mm"
include "mp3an1.mm"

theorem honegdi
  let cT: class T
  let cU: class U


  assert |- ( ( T : ~H --> ~H /\ U : ~H --> ~H ) -> ( -u 1 .op ( T +op U ) ) = ( ( -u 1 .op T ) +op ( -u 1 .op U ) ) )

  proof
    c1
    cneg
    #
    cc
    wcel
    chil
    chil
    cT
    wf
    chil
    chil
    cU
    wf
    @0
    cT
    cU
    chos
    co
    chot
    co
    @0
    cT
    chot
    co
    @0
    cU
    chot
    co
    chos
    co
    wceq
    neg1cn
    @0
    cT
    cU
    hoadddi
    mp3an1
end
