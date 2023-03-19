include "tv.mm"
include "wv.mm"
include "ax-17.mm"
include "ke.mm"
include "kbr.mm"
include "eqtypi.mm"
include "cbvf.mm"

theorem cbv
  param hal: type al
  param hbe: type be
  param vx: var x
  param vy: var y
  param ta: term A
  param tb: term B
  let vz: var z
  assume cbv.1: |- A : be
  assume cbv.2: |- [ x : al = y : al ] |= [ A = B ]

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint al x
  disjoint al y
  disjoint be y
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint B z
  disjoint al z
  assert |- T. |= [ \ x : al . A = \ y : al . B ]

  proof
    hal
    hbe
    vx
    vy
    vz
    ta
    tb
    cbv.1
    hal
    hbe
    vy
    ta
    hal
    vz
    tv
    #
    cbv.1
    hal
    vz
    wv
    #
    ax-17
    hal
    hbe
    vx
    tb
    @0
    hbe
    ta
    tb
    hal
    vx
    tv
    hal
    vy
    tv
    ke
    kbr
    cbv.1
    cbv.2
    eqtypi
    @1
    ax-17
    cbv.2
    cbvf
end
