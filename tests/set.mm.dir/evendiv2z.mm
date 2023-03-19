include "ceven.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "iseven.mm"
include "simprbi.mm"

theorem evendiv2z
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Even -> ( Z / 2 ) e. ZZ )

  proof
    cZ
    ceven
    wcel
    cZ
    cz
    wcel
    cZ
    c2
    cdiv
    co
    cz
    wcel
    cZ
    iseven
    simprbi
end
