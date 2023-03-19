include "kl.mm"
include "tv.mm"
include "kc.mm"
include "ke.mm"
include "kt.mm"
include "weq.mm"
include "wl.mm"
include "wv.mm"
include "wc.mm"
include "ax-beta.mm"
include "dfov2.mm"

theorem beta
  param hal: type al
  param hbe: type be
  param vx: var x
  param ta: term A
  assume beta.1: |- A : be


  assert |- T. |= [ ( \ x : al . A x : al ) = A ]

  proof
    hbe
    hbe
    hal
    vx
    ta
    kl
    #
    hal
    vx
    tv
    #
    kc
    ta
    ke
    kt
    hbe
    weq
    hal
    hbe
    @0
    @1
    hal
    hbe
    vx
    ta
    beta.1
    wl
    hal
    vx
    wv
    wc
    beta.1
    hal
    hbe
    vx
    ta
    beta.1
    ax-beta
    dfov2
end
