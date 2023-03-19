include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "cexp.mm"
include "co.mm"
include "wss.mm"
include "neg1z.mm"
include "1z.mm"
include "prssi.mm"
include "mp2an.mm"
include "m1expcl2.mm"
include "sseldi.mm"

theorem m1expcl
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( N e. ZZ -> ( -u 1 ^ N ) e. ZZ )

  proof
    cN
    cz
    wcel
    c1
    cneg
    #
    c1
    cpr
    #
    cz
    @0
    cN
    cexp
    co
    @0
    cz
    wcel
    c1
    cz
    wcel
    @1
    cz
    wss
    neg1z
    1z
    @0
    c1
    cz
    prssi
    mp2an
    cN
    m1expcl2
    sseldi
end
