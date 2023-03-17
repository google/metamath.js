include "kl.mm"
include "kc.mm"
include "kct.mm"
include "eqtypi.mm"
include "wl.mm"
include "wc.mm"
include "ke.mm"
include "kbr.mm"
include "leq.mm"
include "ceq1.mm"
include "ax-cb1.mm"
include "wctl.mm"
include "adantl.mm"
include "3eqtr4i.mm"

theorem hbxfrf
  let hal: type al
  let hbe: type be
  let vx: var x
  let ta: term A
  let tb: term B
  let tr: term R
  let ts: term S
  let tt: term T
  assume hbxfr.1: |- T : be
  assume hbxfr.2: |- B : al
  assume hbxfrf.3: |- R |= [ T = A ]
  assume hbxfrf.4: |- ( S , R ) |= [ ( \ x : al . A B ) = A ]

  disjoint R x
  assert |- ( S , R ) |= [ ( \ x : al . T B ) = T ]

  proof
    hbe
    hal
    vx
    ta
    kl
    #
    tb
    kc
    #
    ta
    ts
    tr
    kct
    #
    hal
    vx
    tt
    kl
    #
    tb
    kc
    #
    tt
    hal
    hbe
    @0
    tb
    hal
    hbe
    vx
    ta
    hbe
    tt
    ta
    tr
    hbxfr.1
    hbxfrf.3
    eqtypi
    wl
    hbxfr.2
    wc
    hbxfrf.4
    tr
    ts
    @4
    @1
    ke
    kbr
    hal
    hbe
    tb
    @3
    tr
    @0
    hal
    hbe
    vx
    tt
    hbxfr.1
    wl
    hbxfr.2
    hal
    hbe
    vx
    tt
    ta
    tr
    hbxfr.1
    hbxfrf.3
    leq
    ceq1
    ts
    tr
    @1
    ta
    ke
    kbr
    @2
    hbxfrf.4
    ax-cb1
    wctl
    #
    adantl
    tr
    ts
    tt
    ta
    ke
    kbr
    hbxfrf.3
    @5
    adantl
    3eqtr4i
end
