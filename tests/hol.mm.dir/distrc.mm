include "kc.mm"
include "kl.mm"
include "ke.mm"
include "kt.mm"
include "weq.mm"
include "wc.mm"
include "wl.mm"
include "ht.mm"
include "ax-distrc.mm"
include "dfov2.mm"

theorem distrc
  let hal: type al
  let hbe: type be
  let hga: type ga
  let vx: var x
  let ta: term A
  let tb: term B
  let tf: term F
  assume distrc.1: |- F : ( be -> ga )
  assume distrc.2: |- A : be
  assume distrc.3: |- B : al


  assert |- T. |= [ ( \ x : al . ( F A ) B ) = ( ( \ x : al . F B ) ( \ x : al . A B ) ) ]

  proof
    hga
    hga
    hal
    vx
    tf
    ta
    kc
    #
    kl
    #
    tb
    kc
    hal
    vx
    tf
    kl
    #
    tb
    kc
    #
    hal
    vx
    ta
    kl
    #
    tb
    kc
    #
    kc
    ke
    kt
    hga
    weq
    hal
    hga
    @1
    tb
    hal
    hga
    vx
    @0
    hbe
    hga
    tf
    ta
    distrc.1
    distrc.2
    wc
    wl
    distrc.3
    wc
    hbe
    hga
    @3
    @5
    hal
    hbe
    hga
    ht
    #
    @2
    tb
    hal
    @6
    vx
    tf
    distrc.1
    wl
    distrc.3
    wc
    hal
    hbe
    @4
    tb
    hal
    hbe
    vx
    ta
    distrc.2
    wl
    distrc.3
    wc
    wc
    hal
    hbe
    hga
    vx
    ta
    tb
    tf
    distrc.2
    distrc.3
    distrc.1
    ax-distrc
    dfov2
end
