include "kc.mm"
include "kl.mm"
include "wc.mm"
include "wl.mm"
include "ke.mm"
include "kbr.mm"
include "ax-cb1.mm"
include "distrc.mm"
include "a1i.mm"
include "ht.mm"
include "eqtypri.mm"
include "ceq12.mm"
include "eqtri.mm"

theorem hbc
  let hal: type al
  let hbe: type be
  let hga: type ga
  let vx: var x
  let ta: term A
  let tb: term B
  let tf: term F
  let tr: term R
  assume hbc.1: |- F : ( be -> ga )
  assume hbc.2: |- A : be
  assume hbc.3: |- B : al
  assume hbc.4: |- R |= [ ( \ x : al . F B ) = F ]
  assume hbc.5: |- R |= [ ( \ x : al . A B ) = A ]


  assert |- R |= [ ( \ x : al . ( F A ) B ) = ( F A ) ]

  proof
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
    #
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
    tb
    kc
    #
    kc
    #
    @0
    tr
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
    hbc.1
    hbc.2
    wc
    wl
    hbc.3
    wc
    @2
    @6
    ke
    kbr
    tr
    @4
    tf
    ke
    kbr
    tr
    hbc.4
    ax-cb1
    hal
    hbe
    hga
    vx
    ta
    tb
    tf
    hbc.1
    hbc.2
    hbc.3
    distrc
    a1i
    hbe
    hga
    @5
    ta
    @4
    tr
    tf
    hal
    hbe
    hga
    ht
    #
    @3
    tb
    hal
    @7
    vx
    tf
    hbc.1
    wl
    hbc.3
    wc
    hbe
    ta
    @5
    tr
    hbc.2
    hbc.5
    eqtypri
    hbc.4
    hbc.5
    ceq12
    eqtri
end
