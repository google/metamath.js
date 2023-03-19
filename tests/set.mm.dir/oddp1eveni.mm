include "codd.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "c2.mm"
include "cdiv.mm"
include "ceven.mm"
include "oddz.mm"
include "peano2zd.mm"
include "oddp1div2z.mm"
include "iseven.mm"
include "sylanbrc.mm"

theorem oddp1eveni
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd -> ( Z + 1 ) e. Even )

  proof
    cZ
    codd
    wcel
    #
    cZ
    c1
    caddc
    co
    #
    cz
    wcel
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
    cZ
    oddz
    peano2zd
    cZ
    oddp1div2z
    @1
    iseven
    sylanbrc
end
