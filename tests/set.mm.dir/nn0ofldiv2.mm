include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "nn0z.mm"
include "zofldiv2.mm"
include "syl2an.mm"

theorem nn0ofldiv2
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ ( ( N + 1 ) / 2 ) e. NN0 ) -> ( |_ ` ( N / 2 ) ) = ( ( N - 1 ) / 2 ) )

  proof
    cN
    cn0
    wcel
    cN
    cz
    wcel
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    #
    cz
    wcel
    cN
    c2
    cdiv
    co
    cfl
    cfv
    cN
    c1
    cmin
    co
    c2
    cdiv
    co
    wceq
    @0
    cn0
    wcel
    cN
    nn0z
    @0
    nn0z
    cN
    zofldiv2
    syl2an
end
