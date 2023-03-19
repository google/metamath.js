include "kt.mm"
include "tal.mm"
include "tim.mm"
include "kbr.mm"
include "kl.mm"
include "kc.mm"
include "kct.mm"
include "ax4.mm"
include "hb.mm"
include "ht.mm"
include "wal.mm"
include "wim.mm"
include "wov.mm"
include "wl.mm"
include "wc.mm"
include "adantl.mm"
include "ax-cb1.mm"
include "adantr.mm"
include "mpd.mm"
include "tv.mm"
include "wv.mm"
include "ax-17.mm"
include "ax-hbl1.mm"
include "hbc.mm"
include "hbct.mm"
include "alrimi.mm"
include "ex.mm"
include "wtru.mm"

theorem ax5
  param hal: type al
  param vx: var x
  param tr: term R
  param ts: term S
  let vy: var y
  assume ax5.1: |- R : bool
  assume ax5.2: |- S : bool

  disjoint al x
  disjoint R y
  disjoint S y
  disjoint x y
  disjoint al y
  assert |- T. |= [ ( ! \ x : al . [ R ==> S ] ) ==> [ ( ! \ x : al . R ) ==> ( ! \ x : al . S ) ] ]

  proof
    kt
    tal
    hal
    vx
    tr
    ts
    tim
    kbr
    #
    kl
    #
    kc
    #
    tal
    hal
    vx
    tr
    kl
    #
    kc
    #
    tal
    hal
    vx
    ts
    kl
    kc
    #
    tim
    kbr
    #
    @2
    kt
    @6
    @2
    @4
    @5
    hal
    vx
    vy
    ts
    @2
    @4
    kct
    #
    @7
    tr
    ts
    ax5.2
    @4
    @2
    tr
    hal
    vx
    tr
    ax5.1
    ax4
    #
    hal
    hb
    ht
    #
    hb
    tal
    @1
    hal
    wal
    #
    hal
    hb
    vx
    @0
    hb
    hb
    hb
    tr
    ts
    tim
    wim
    ax5.1
    ax5.2
    wov
    #
    wl
    #
    wc
    #
    adantl
    @2
    @4
    @0
    hal
    vx
    @0
    @11
    ax4
    tr
    @4
    @8
    ax-cb1
    #
    adantr
    mpd
    hal
    vx
    @2
    hal
    vy
    tv
    #
    @4
    kt
    @13
    hal
    vy
    wv
    #
    @14
    hal
    @9
    hb
    vx
    @1
    @15
    tal
    kt
    @10
    @12
    @16
    hal
    @9
    hb
    ht
    vx
    tal
    @15
    @10
    @16
    ax-17
    #
    hal
    hal
    hb
    vx
    @0
    @15
    @11
    @16
    ax-hbl1
    hbc
    hal
    @9
    hb
    vx
    @3
    @15
    tal
    kt
    @10
    hal
    hb
    vx
    tr
    ax5.1
    wl
    @16
    @17
    hal
    hal
    hb
    vx
    tr
    @15
    ax5.1
    @16
    ax-hbl1
    hbc
    hbct
    alrimi
    ex
    wtru
    adantl
    ex
end
