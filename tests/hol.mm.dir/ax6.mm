include "tne.mm"
include "tal.mm"
include "kl.mm"
include "kc.mm"
include "hb.mm"
include "wnot.mm"
include "ht.mm"
include "wal.mm"
include "wl.mm"
include "wc.mm"
include "tv.mm"
include "kt.mm"
include "wv.mm"
include "ax-17.mm"
include "ax-hbl1.mm"
include "hbc.mm"
include "isfree.mm"

theorem ax6
  let hal: type al
  let vx: var x
  let tr: term R
  let vy: var y
  assume ax6.1: |- R : bool

  disjoint al x
  disjoint R y
  disjoint x y
  disjoint al y
  assert |- T. |= [ ( ~ ( ! \ x : al . R ) ) ==> ( ! \ x : al . ( ~ ( ! \ x : al . R ) ) ) ]

  proof
    hal
    vx
    vy
    tne
    tal
    hal
    vx
    tr
    kl
    #
    kc
    #
    kc
    hb
    hb
    tne
    @1
    wnot
    hal
    hb
    ht
    #
    hb
    tal
    @0
    hal
    wal
    #
    hal
    hb
    vx
    tr
    ax6.1
    wl
    #
    wc
    #
    wc
    hal
    hb
    hb
    vx
    @1
    hal
    vy
    tv
    #
    tne
    kt
    wnot
    @5
    hal
    vy
    wv
    #
    hal
    hb
    hb
    ht
    vx
    tne
    @6
    wnot
    @7
    ax-17
    hal
    @2
    hb
    vx
    @0
    @6
    tal
    kt
    @3
    @4
    @7
    hal
    @2
    hb
    ht
    vx
    tal
    @6
    @3
    @7
    ax-17
    hal
    hal
    hb
    vx
    tr
    @6
    ax6.1
    @7
    ax-hbl1
    hbc
    hbc
    isfree
end
