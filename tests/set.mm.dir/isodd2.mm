include "codd.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wa.mm"
include "cmin.mm"
include "isodd.mm"
include "zob.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isodd2
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd <-> ( Z e. ZZ /\ ( ( Z - 1 ) / 2 ) e. ZZ ) )

  proof
    cZ
    codd
    wcel
    cZ
    cz
    wcel
    #
    cZ
    c1
    caddc
    co
    c2
    cdiv
    co
    cz
    wcel
    #
    wa
    @0
    cZ
    c1
    cmin
    co
    c2
    cdiv
    co
    cz
    wcel
    #
    wa
    cZ
    isodd
    @0
    @1
    @2
    cZ
    zob
    pm5.32i
    bitri
end
