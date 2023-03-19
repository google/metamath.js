include "kl.mm"
include "kc.mm"
include "ke.mm"
include "kbr.mm"
include "ax-cb1.mm"
include "id.mm"
include "adantr.mm"
include "hbxfrf.mm"
include "syl2anc.mm"

theorem hbxfr
  let hal: type al
  let hbe: type be
  let vx: var x
  let ta: term A
  let tb: term B
  let tr: term R
  let tt: term T
  assume hbxfr.1: |- T : be
  assume hbxfr.2: |- B : al
  assume hbxfr.3: |- R |= [ T = A ]
  assume hbxfr.4: |- R |= [ ( \ x : al . A B ) = A ]

  disjoint R x
  assert |- R |= [ ( \ x : al . T B ) = T ]

  proof
    hal
    vx
    tt
    kl
    tb
    kc
    tt
    ke
    kbr
    tr
    tr
    tr
    tr
    tt
    ta
    ke
    kbr
    tr
    hbxfr.3
    ax-cb1
    #
    id
    #
    @1
    hal
    hbe
    vx
    ta
    tb
    tr
    tr
    tt
    hbxfr.1
    hbxfr.2
    hbxfr.3
    tr
    tr
    hal
    vx
    ta
    kl
    tb
    kc
    ta
    ke
    kbr
    hbxfr.4
    @0
    adantr
    hbxfrf
    syl2anc
end
