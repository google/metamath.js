include "ceven.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "iseven.mm"
include "simplbi.mm"

theorem evenz
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Even -> Z e. ZZ )

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
    simplbi
end
