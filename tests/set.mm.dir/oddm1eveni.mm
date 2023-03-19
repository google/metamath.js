include "codd.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cz.mm"
include "c2.mm"
include "cdiv.mm"
include "ceven.mm"
include "oddz.mm"
include "peano2zm.mm"
include "syl.mm"
include "oddm1div2z.mm"
include "iseven.mm"
include "sylanbrc.mm"

theorem oddm1eveni
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd -> ( Z - 1 ) e. Even )

  proof
    cZ
    codd
    wcel
    #
    cZ
    c1
    cmin
    co
    #
    cz
    wcel
    #
    @1
    c2
    cdiv
    co
    cz
    wcel
    @1
    ceven
    wcel
    @0
    cZ
    cz
    wcel
    @2
    cZ
    oddz
    cZ
    peano2zm
    syl
    cZ
    oddm1div2z
    @1
    iseven
    sylanbrc
end
