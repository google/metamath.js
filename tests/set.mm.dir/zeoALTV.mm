include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "wo.mm"
include "ceven.mm"
include "codd.mm"
include "zeo.mm"
include "ancli.mm"
include "andi.mm"
include "sylib.mm"
include "iseven.mm"
include "isodd.mm"
include "orbi12i.mm"
include "sylibr.mm"

theorem zeoALTV
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. ZZ -> ( Z e. Even \/ Z e. Odd ) )

  proof
    cZ
    cz
    wcel
    #
    @0
    cZ
    c2
    cdiv
    co
    cz
    wcel
    #
    wa
    #
    @0
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
    #
    wo
    #
    cZ
    ceven
    wcel
    #
    cZ
    codd
    wcel
    #
    wo
    @0
    @0
    @1
    @3
    wo
    #
    wa
    @5
    @0
    @8
    cZ
    zeo
    ancli
    @0
    @1
    @3
    andi
    sylib
    @6
    @2
    @7
    @4
    cZ
    iseven
    cZ
    isodd
    orbi12i
    sylibr
end
