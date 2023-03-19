include "tal.mm"
include "kl.mm"
include "kc.mm"
include "kct.mm"
include "ax-cb1.mm"
include "wctr.mm"
include "ax4.mm"
include "wctl.mm"
include "adantl.mm"
include "syldan.mm"
include "tv.mm"
include "kt.mm"
include "wv.mm"
include "hb.mm"
include "ht.mm"
include "wal.mm"
include "wl.mm"
include "wc.mm"
include "ax-17.mm"
include "ax-hbl1.mm"
include "hbc.mm"
include "hbct.mm"
include "alrimi.mm"

theorem alimdv
  param hal: type al
  param vx: var x
  param ta: term A
  param tb: term B
  param tr: term R
  let vy: var y
  assume alimdv.1: |- ( R , A ) |= B

  disjoint R x
  disjoint al x
  disjoint A y
  disjoint B y
  disjoint x y
  disjoint R y
  disjoint al y
  assert |- ( R , ( ! \ x : al . A ) ) |= ( ! \ x : al . B )

  proof
    hal
    vx
    vy
    tb
    tr
    tal
    hal
    vx
    ta
    kl
    #
    kc
    #
    kct
    tb
    tr
    @1
    ta
    @1
    tr
    ta
    hal
    vx
    ta
    tr
    ta
    tb
    tr
    ta
    kct
    alimdv.1
    ax-cb1
    #
    wctr
    #
    ax4
    tr
    ta
    @2
    wctl
    #
    adantl
    alimdv.1
    syldan
    hal
    vx
    tr
    hal
    vy
    tv
    #
    @1
    kt
    @4
    hal
    vy
    wv
    #
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
    ta
    @3
    wl
    #
    wc
    hal
    hb
    vx
    tr
    @5
    @4
    @6
    ax-17
    hal
    @7
    hb
    vx
    @0
    @5
    tal
    kt
    @8
    @9
    @6
    hal
    @7
    hb
    ht
    vx
    tal
    @5
    @8
    @6
    ax-17
    hal
    hal
    hb
    vx
    ta
    @5
    @3
    @6
    ax-hbl1
    hbc
    hbct
    alrimi
end
