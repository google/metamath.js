include "kt.mm"
include "tne.mm"
include "tal.mm"
include "tv.mm"
include "ke.mm"
include "kbr.mm"
include "kl.mm"
include "kc.mm"
include "tim.mm"
include "wv.mm"
include "weqi.mm"
include "hb.mm"
include "ax-17.mm"
include "isfree.mm"
include "wnot.mm"
include "ht.mm"
include "wal.mm"
include "wl.mm"
include "wc.mm"
include "adantr.mm"
include "ex.mm"

theorem ax12
  param hal: type al
  param vx: var x
  param vy: var y
  param vz: var z
  let vp: var p

  disjoint x z
  disjoint y z
  disjoint al z
  disjoint p x
  disjoint p z
  disjoint p y
  disjoint al p
  assert |- T. |= [ ( ~ ( ! \ z : al . [ z : al = x : al ] ) ) ==> [ ( ~ ( ! \ z : al . [ z : al = y : al ] ) ) ==> [ [ x : al = y : al ] ==> ( ! \ z : al . [ x : al = y : al ] ) ] ] ]

  proof
    kt
    tne
    tal
    hal
    vz
    hal
    vz
    tv
    #
    hal
    vx
    tv
    #
    ke
    kbr
    #
    kl
    #
    kc
    #
    kc
    #
    tne
    tal
    hal
    vz
    @0
    hal
    vy
    tv
    #
    ke
    kbr
    #
    kl
    #
    kc
    #
    kc
    #
    @1
    @6
    ke
    kbr
    #
    tal
    hal
    vz
    @11
    kl
    kc
    tim
    kbr
    #
    tim
    kbr
    #
    kt
    @5
    @13
    kt
    @10
    @12
    kt
    @10
    @12
    hal
    vz
    vp
    @11
    hal
    @1
    @6
    hal
    vx
    wv
    #
    hal
    vy
    wv
    #
    weqi
    #
    hal
    hb
    vz
    @11
    hal
    vp
    tv
    @16
    hal
    vp
    wv
    ax-17
    isfree
    hb
    hb
    tne
    @9
    wnot
    hal
    hb
    ht
    #
    hb
    tal
    @8
    hal
    wal
    #
    hal
    hb
    vz
    @7
    hal
    @0
    @6
    hal
    vz
    wv
    #
    @15
    weqi
    wl
    wc
    wc
    adantr
    ex
    hb
    hb
    tne
    @4
    wnot
    @17
    hb
    tal
    @3
    @18
    hal
    hb
    vz
    @2
    hal
    @0
    @1
    @19
    @14
    weqi
    wl
    wc
    wc
    adantr
    ex
end
