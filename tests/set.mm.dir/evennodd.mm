include "ceven.mm"
include "wcel.mm"
include "cz.mm"
include "wn.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wo.mm"
include "codd.mm"
include "wa.mm"
include "iseven.mm"
include "zeo2.mm"
include "biimpd.mm"
include "imp.mm"
include "sylbi.mm"
include "olcd.mm"
include "isodd.mm"
include "notbii.mm"
include "ianor.mm"
include "bitri.mm"
include "sylibr.mm"

theorem evennodd
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Even -> -. Z e. Odd )

  proof
    cZ
    ceven
    wcel
    #
    cZ
    cz
    wcel
    #
    wn
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
    wn
    #
    wo
    #
    cZ
    codd
    wcel
    #
    wn
    #
    @0
    @4
    @2
    @0
    @1
    cZ
    c2
    cdiv
    co
    cz
    wcel
    #
    wa
    @4
    cZ
    iseven
    @1
    @8
    @4
    @1
    @8
    @4
    cZ
    zeo2
    biimpd
    imp
    sylbi
    olcd
    @7
    @1
    @3
    wa
    #
    wn
    @5
    @6
    @9
    cZ
    isodd
    notbii
    @1
    @3
    ianor
    bitri
    sylibr
end
