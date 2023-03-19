include "ht.mm"
include "kl.mm"
include "kc.mm"
include "wl.mm"
include "wc.mm"
include "ke.mm"
include "kbr.mm"
include "ax-cb1.mm"
include "distrl.mm"
include "a1i.mm"
include "leq.mm"
include "eqtri.mm"

theorem hbl
  let hal: type al
  let hbe: type be
  let hga: type ga
  let vx: var x
  let vy: var y
  let ta: term A
  let tb: term B
  let tr: term R
  assume hbl.1: |- A : ga
  assume hbl.2: |- B : al
  assume hbl.3: |- R |= [ ( \ x : al . A B ) = A ]

  disjoint x y
  disjoint B y
  disjoint R y
  assert |- R |= [ ( \ x : al . \ y : be . A B ) = \ y : be . A ]

  proof
    hbe
    hga
    ht
    #
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
    #
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
    #
    @1
    tr
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
    hbl.1
    wl
    wl
    hbl.2
    wc
    @3
    @6
    ke
    kbr
    tr
    @5
    ta
    ke
    kbr
    tr
    hbl.3
    ax-cb1
    hal
    hbe
    hga
    vx
    vy
    ta
    tb
    hbl.1
    hbl.2
    distrl
    a1i
    hbe
    hga
    vy
    @5
    ta
    tr
    hal
    hga
    @4
    tb
    hal
    hga
    vx
    ta
    hbl.1
    wl
    hbl.2
    wc
    hbl.3
    leq
    eqtri
end
