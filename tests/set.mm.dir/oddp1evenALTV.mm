include "cz.mm"
include "wcel.mm"
include "codd.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "ceven.mm"
include "isodd.mm"
include "baib.mm"
include "peano2z.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "iseven.mm"
include "syl6bbr.mm"

theorem oddp1evenALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. ZZ -> ( N e. Odd <-> ( N + 1 ) e. Even ) )

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
    caddc
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
    isodd
    baib
    @0
    @3
    @4
    cN
    peano2z
    biantrurd
    bitrd
    @2
    iseven
    syl6bbr
end
