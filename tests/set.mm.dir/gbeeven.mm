include "cgbe.mm"
include "wcel.mm"
include "ceven.mm"
include "cv.mm"
include "codd.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cprime.mm"
include "wrex.mm"
include "isgbe.mm"
include "simplbi.mm"

theorem gbeeven
  let cZ: class Z
  let vz: setvar z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. GoldbachEven -> Z e. Even )

  proof
    cZ
    cgbe
    wcel
    cZ
    ceven
    wcel
    vp
    cv
    #
    codd
    wcel
    vq
    cv
    #
    codd
    wcel
    cZ
    @0
    @1
    caddc
    co
    wceq
    w3a
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    cZ
    vq
    vp
    isgbe
    simplbi
end
