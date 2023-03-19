include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cz.mm"
include "wcel.mm"
include "codd.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "df-odd.mm"
include "elrab2.mm"

theorem isodd
  let cZ: class Z
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd <-> ( Z e. ZZ /\ ( ( Z + 1 ) / 2 ) e. ZZ ) )

  proof
    vz
    cv
    #
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    cZ
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    vz
    cZ
    cz
    codd
    @0
    cZ
    wceq
    #
    @2
    @4
    cz
    @5
    @1
    @3
    c2
    cdiv
    @0
    cZ
    c1
    caddc
    oveq1
    oveq1d
    eleq1d
    vz
    df-odd
    elrab2
end
