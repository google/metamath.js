include "ceven.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "iseven2.mm"
include "simprbi.mm"

theorem 2dvdseven
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Even -> 2 || Z )

  proof
    cZ
    ceven
    wcel
    cZ
    cz
    wcel
    c2
    cZ
    cdvds
    wbr
    cZ
    iseven2
    simprbi
end
