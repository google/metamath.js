include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wn.mm"
include "nneo.mm"
include "biimprd.mm"
include "orrd.mm"
include "orcomd.mm"

theorem nneop
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( ( N / 2 ) e. NN \/ ( ( N + 1 ) / 2 ) e. NN ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    cn
    wcel
    #
    cN
    c2
    cdiv
    co
    cn
    wcel
    #
    @0
    @1
    @2
    @0
    @2
    @1
    wn
    cN
    nneo
    biimprd
    orrd
    orcomd
end
