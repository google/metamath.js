include "kt.mm"
include "tal.mm"
include "tv.mm"
include "kc.mm"
include "ke.mm"
include "kbr.mm"
include "kl.mm"
include "hb.mm"
include "ht.mm"
include "wv.mm"
include "wc.mm"
include "wl.mm"
include "weqi.mm"
include "ax4.mm"
include "wal.mm"
include "ax-17.mm"
include "ax-hbl1.mm"
include "hbc.mm"
include "leqf.mm"
include "ax-cb1.mm"
include "eta.mm"
include "a1i.mm"
include "3eqtr3i.mm"
include "wtru.mm"
include "adantl.mm"
include "ex.mm"

theorem axext
  param hal: type al
  param vx: var x
  param ta: term A
  param tb: term B
  let vy: var y
  assume axext.1: |- A : ( al -> bool )
  assume axext.2: |- B : ( al -> bool )

  disjoint A x
  disjoint B x
  disjoint al x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint al y
  assert |- T. |= [ ( ! \ x : al . [ ( A x : al ) = ( B x : al ) ] ) ==> [ A = B ] ]

  proof
    kt
    tal
    hal
    vx
    ta
    hal
    vx
    tv
    #
    kc
    #
    tb
    @0
    kc
    #
    ke
    kbr
    #
    kl
    #
    kc
    #
    ta
    tb
    ke
    kbr
    #
    @5
    kt
    @6
    hal
    hb
    ht
    #
    hal
    vx
    @1
    kl
    #
    hal
    vx
    @2
    kl
    #
    @5
    ta
    tb
    hal
    hb
    vx
    @1
    hal
    hb
    ta
    @0
    axext.1
    hal
    vx
    wv
    #
    wc
    #
    wl
    hal
    hb
    vx
    vy
    @1
    @2
    @5
    @11
    hal
    vx
    @3
    hb
    @1
    @2
    @11
    hal
    hb
    tb
    @0
    axext.2
    @10
    wc
    weqi
    #
    ax4
    hal
    @7
    hb
    vx
    @4
    hal
    vy
    tv
    #
    tal
    kt
    hal
    wal
    #
    hal
    hb
    vx
    @3
    @12
    wl
    hal
    vy
    wv
    #
    hal
    @7
    hb
    ht
    vx
    tal
    @13
    @14
    @15
    ax-17
    hal
    hal
    hb
    vx
    @3
    @13
    @12
    @15
    ax-hbl1
    hbc
    leqf
    #
    @8
    ta
    ke
    kbr
    @5
    @8
    @9
    ke
    kbr
    @5
    @16
    ax-cb1
    #
    hal
    hb
    vx
    ta
    axext.1
    eta
    a1i
    @9
    tb
    ke
    kbr
    @5
    @17
    hal
    hb
    vx
    tb
    axext.2
    eta
    a1i
    3eqtr3i
    wtru
    adantl
    ex
end
