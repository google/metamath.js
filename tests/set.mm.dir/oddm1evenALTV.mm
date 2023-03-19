include "cz.mm"
include "wcel.mm"
include "codd.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "ceven.mm"
include "isodd2.mm"
include "baib.mm"
include "peano2zm.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "iseven.mm"
include "syl6bbr.mm"

theorem oddm1evenALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. ZZ -> ( N e. Odd <-> ( N - 1 ) e. Even ) )

  proof
    cN
    cz
    wcel
    #
    cN
    codd
    wcel
    #
    cN
    c1
    cmin
    co
    #
    cz
    wcel
    #
    @2
    c2
    cdiv
    co
    cz
    wcel
    #
    wa
    #
    @2
    ceven
    wcel
    @0
    @1
    @4
    @5
    @1
    @0
    @4
    cN
    isodd2
    baib
    @0
    @3
    @4
    cN
    peano2zm
    biantrurd
    bitrd
    @2
    iseven
    syl6bbr
end
