include "codd.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "isodd.mm"
include "simprbi.mm"

theorem oddp1div2z
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd -> ( ( Z + 1 ) / 2 ) e. ZZ )

  proof
    cZ
    codd
    wcel
    cZ
    cz
    wcel
    cZ
    c1
    caddc
    co
    c2
    cdiv
    co
    cz
    wcel
    cZ
    isodd
    simprbi
end
