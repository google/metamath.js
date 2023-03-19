include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "c1.mm"
include "cpr.mm"
include "cn.mm"
include "2nn.mm"
include "zmodfzo.mm"
include "ancoms.mm"
include "mpan.mm"
include "fzo0to2pr.mm"
include "syl6eleq.mm"

theorem elmod2
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. ZZ -> ( N mod 2 ) e. { 0 , 1 } )

  proof
    cN
    cz
    wcel
    #
    cN
    c2
    cmo
    co
    #
    cc0
    c2
    cfzo
    co
    #
    cc0
    c1
    cpr
    c2
    cn
    wcel
    #
    @0
    @1
    @2
    wcel
    #
    2nn
    @0
    @3
    @4
    cN
    c2
    zmodfzo
    ancoms
    mpan
    fzo0to2pr
    syl6eleq
end
