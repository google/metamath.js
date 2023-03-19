include "ht.mm"
include "kl.mm"
include "kc.mm"
include "ke.mm"
include "kt.mm"
include "weq.mm"
include "wl.mm"
include "wc.mm"
include "ax-distrl.mm"
include "dfov2.mm"

theorem distrl
  param hal: type al
  param hbe: type be
  param hga: type ga
  param vx: var x
  param vy: var y
  param ta: term A
  param tb: term B
  assume distrl.1: |- A : ga
  assume distrl.2: |- B : al

  disjoint x y
  disjoint B y
  assert |- T. |= [ ( \ x : al . \ y : be . A B ) = \ y : be . ( \ x : al . A B ) ]

  proof
    hbe
    hga
    ht
    #
    @0
    hal
    vx
    hbe
    vy
    ta
    kl
    #
    kl
    #
    tb
    kc
    hbe
    vy
    hal
    vx
    ta
    kl
    #
    tb
    kc
    #
    kl
    ke
    kt
    @0
    weq
    hal
    @0
    @2
    tb
    hal
    @0
    vx
    @1
    hbe
    hga
    vy
    ta
    distrl.1
    wl
    wl
    distrl.2
    wc
    hbe
    hga
    vy
    @4
    hal
    hga
    @3
    tb
    hal
    hga
    vx
    ta
    distrl.1
    wl
    distrl.2
    wc
    wl
    hal
    hbe
    hga
    vx
    vy
    ta
    tb
    distrl.1
    distrl.2
    ax-distrl
    dfov2
end
