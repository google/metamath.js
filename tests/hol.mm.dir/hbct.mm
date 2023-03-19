include "kt.mm"
include "kct.mm"
include "kl.mm"
include "kc.mm"
include "ke.mm"
include "kbr.mm"
include "ax-cb1.mm"
include "trud.mm"
include "hb.mm"
include "tan.mm"
include "wct.mm"
include "wan.mm"
include "wov.mm"
include "dfan2.mm"
include "eqcomi.mm"
include "ht.mm"
include "a17i.mm"
include "hbov.mm"
include "wtru.mm"
include "adantr.mm"
include "hbxfrf.mm"
include "mpdan.mm"

theorem hbct
  let hal: type al
  let vx: var x
  let ta: term A
  let tb: term B
  let tc: term C
  let tr: term R
  assume hbct.1: |- A : bool
  assume hbct.2: |- B : al
  assume hbct.3: |- C : bool
  assume hbct.4: |- R |= [ ( \ x : al . A B ) = A ]
  assume hbct.5: |- R |= [ ( \ x : al . C B ) = C ]


  assert |- R |= [ ( \ x : al . ( A , C ) B ) = ( A , C ) ]

  proof
    tr
    kt
    hal
    vx
    ta
    tc
    kct
    #
    kl
    tb
    kc
    @0
    ke
    kbr
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
    tr
    hbct.4
    ax-cb1
    #
    trud
    hal
    hb
    vx
    ta
    tc
    tan
    kbr
    #
    tb
    kt
    tr
    @0
    ta
    tc
    hbct.1
    hbct.3
    wct
    hbct.2
    hb
    @2
    @0
    kt
    hb
    hb
    hb
    ta
    tc
    tan
    wan
    hbct.1
    hbct.3
    wov
    ta
    tc
    hbct.1
    hbct.3
    dfan2
    eqcomi
    tr
    kt
    hal
    vx
    @2
    kl
    tb
    kc
    @2
    ke
    kbr
    hal
    hb
    hb
    hb
    vx
    ta
    tb
    tc
    tan
    tr
    wan
    hbct.1
    hbct.2
    hbct.3
    hal
    hb
    hb
    hb
    ht
    ht
    vx
    tan
    tb
    tr
    wan
    hbct.2
    @1
    a17i
    hbct.4
    hbct.5
    hbov
    wtru
    adantr
    hbxfrf
    mpdan
end
