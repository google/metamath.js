include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "cuz.mm"
include "wceq.mm"
include "breq1.mm"
include "rabbidv.mm"
include "df-uz.mm"
include "zex.mm"
include "rabex.mm"
include "fvmpt.mm"

theorem uzval
  let vk: setvar k
  let cN: class N
  let vj: setvar j
  let cM: class M

  disjoint N k
  disjoint j k
  disjoint N j
  disjoint M k
  assert |- ( N e. ZZ -> ( ZZ>= ` N ) = { k e. ZZ | N <_ k } )

  proof
    vj
    cN
    vj
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    vk
    cz
    crab
    cN
    @1
    cle
    wbr
    #
    vk
    cz
    crab
    cz
    cuz
    @0
    cN
    wceq
    @2
    @3
    vk
    cz
    @0
    cN
    @1
    cle
    breq1
    rabbidv
    vj
    vk
    df-uz
    @3
    vk
    cz
    zex
    rabex
    fvmpt
end
