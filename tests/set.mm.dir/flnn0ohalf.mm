include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "nn0ofldiv2.mm"
include "cz.mm"
include "wceq.mm"
include "nn0o.mm"
include "nn0zd.mm"
include "flid.mm"
include "syl.mm"
include "eqtr4d.mm"

theorem flnn0ohalf
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ ( ( N + 1 ) / 2 ) e. NN0 ) -> ( |_ ` ( N / 2 ) ) = ( |_ ` ( ( N - 1 ) / 2 ) ) )

  proof
    cN
    cn0
    wcel
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    cn0
    wcel
    wa
    #
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
    #
    @1
    cfl
    cfv
    #
    cN
    nn0ofldiv2
    @0
    @1
    cz
    wcel
    @2
    @1
    wceq
    @0
    @1
    cN
    nn0o
    nn0zd
    @1
    flid
    syl
    eqtr4d
end
