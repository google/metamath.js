include "codd.mm"
include "wcel.mm"
include "cz.mm"
include "wn.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "wo.mm"
include "ceven.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "isodd.mm"
include "zeo2.mm"
include "biimpd.mm"
include "con2d.mm"
include "imp.mm"
include "sylbi.mm"
include "olcd.mm"
include "ianor.mm"
include "iseven.mm"
include "xchnxbir.mm"
include "sylibr.mm"

theorem oddneven
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd -> -. Z e. Even )

  proof
    cZ
    codd
    wcel
    #
    cZ
    cz
    wcel
    #
    wn
    #
    cZ
    c2
    cdiv
    co
    cz
    wcel
    #
    wn
    #
    wo
    #
    cZ
    ceven
    wcel
    #
    wn
    @0
    @4
    @2
    @0
    @1
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
    @4
    cZ
    isodd
    @1
    @7
    @4
    @1
    @3
    @7
    @1
    @3
    @7
    wn
    cZ
    zeo2
    biimpd
    con2d
    imp
    sylbi
    olcd
    @1
    @3
    wa
    @5
    @6
    @1
    @3
    ianor
    cZ
    iseven
    xchnxbir
    sylibr
end
