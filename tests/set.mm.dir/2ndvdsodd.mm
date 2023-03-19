include "codd.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "isodd3.mm"
include "simprbi.mm"

theorem 2ndvdsodd
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd -> -. 2 || Z )

  proof
    cZ
    codd
    wcel
    cZ
    cz
    wcel
    c2
    cZ
    cdvds
    wbr
    wn
    cZ
    isodd3
    simprbi
end
