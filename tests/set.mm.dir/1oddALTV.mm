include "c1.mm"
include "codd.mm"
include "wcel.mm"
include "cz.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "1z.mm"
include "1p1e2.mm"
include "oveq1i.mm"
include "2div2e1.mm"
include "eqtri.mm"
include "eqeltri.mm"
include "isodd.mm"
include "mpbir2an.mm"

theorem 1oddALTV
  let vk: setvar k
  let vx: setvar x


  assert |- 1 e. Odd

  proof
    c1
    codd
    wcel
    c1
    cz
    wcel
    c1
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
    1z
    @1
    c1
    cz
    @1
    c2
    c2
    cdiv
    co
    c1
    @0
    c2
    c2
    cdiv
    1p1e2
    oveq1i
    2div2e1
    eqtri
    1z
    eqeltri
    c1
    isodd
    mpbir2an
end
