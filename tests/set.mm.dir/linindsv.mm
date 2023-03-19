include "clininds.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "rellininds.mm"
include "brrelexi.mm"
include "brrelex2i.mm"
include "jca.mm"

theorem linindsv
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vx: setvar x


  assert |- ( S linIndS M -> ( S e. _V /\ M e. _V ) )

  proof
    cS
    cM
    clininds
    wbr
    cS
    cvv
    wcel
    cM
    cvv
    wcel
    cS
    cM
    clininds
    rellininds
    brrelexi
    cS
    cM
    clininds
    rellininds
    brrelex2i
    jca
end
