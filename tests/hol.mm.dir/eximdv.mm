include "tex.mm"
include "kl.mm"
include "kc.mm"
include "kct.mm"
include "ax-cb2.mm"
include "19.8a.mm"
include "syl.mm"
include "hb.mm"
include "tv.mm"
include "ax-cb1.mm"
include "wctl.mm"
include "wv.mm"
include "ax-17.mm"
include "ht.mm"
include "kt.mm"
include "wex.mm"
include "wl.mm"
include "ax-hbl1.mm"
include "hbc.mm"
include "exlimd.mm"

theorem eximdv
  let hal: type al
  let vx: var x
  let ta: term A
  let tb: term B
  let tr: term R
  let vy: var y
  assume alimdv.1: |- ( R , A ) |= B

  disjoint R x
  disjoint al x
  disjoint A y
  disjoint B y
  disjoint x y
  disjoint R y
  disjoint al y
  assert |- ( R , ( ? \ x : al . A ) ) |= ( ? \ x : al . B )

  proof
    hal
    vx
    vy
    ta
    tr
    tex
    hal
    vx
    tb
    kl
    #
    kc
    #
    tr
    ta
    kct
    #
    tb
    @1
    alimdv.1
    hal
    vx
    tb
    tb
    @2
    alimdv.1
    ax-cb2
    #
    19.8a
    syl
    hal
    hb
    vx
    tr
    hal
    vy
    tv
    #
    tr
    ta
    tb
    @2
    alimdv.1
    ax-cb1
    wctl
    hal
    vy
    wv
    #
    ax-17
    hal
    hal
    hb
    ht
    #
    hb
    vx
    @0
    @4
    tex
    kt
    hal
    wex
    #
    hal
    hb
    vx
    tb
    @3
    wl
    @5
    hal
    @6
    hb
    ht
    vx
    tex
    @4
    @7
    @5
    ax-17
    hal
    hal
    hb
    vx
    tb
    @4
    @3
    @5
    ax-hbl1
    hbc
    exlimd
end
