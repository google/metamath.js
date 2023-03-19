include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "ceven.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "df-even.mm"
include "elrab2.mm"

theorem iseven
  let cZ: class Z
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Even <-> ( Z e. ZZ /\ ( Z / 2 ) e. ZZ ) )

  proof
    vz
    cv
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    cZ
    c2
    cdiv
    co
    #
    cz
    wcel
    vz
    cZ
    cz
    ceven
    @0
    cZ
    wceq
    @1
    @2
    cz
    @0
    cZ
    c2
    cdiv
    oveq1
    eleq1d
    vz
    df-even
    elrab2
end
