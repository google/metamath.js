include "kt.mm"
include "tv.mm"
include "ke.mm"
include "kbr.mm"
include "tal.mm"
include "kl.mm"
include "kc.mm"
include "tim.mm"
include "kct.mm"
include "hb.mm"
include "ht.mm"
include "wal.mm"
include "wl.mm"
include "wc.mm"
include "id.mm"
include "wv.mm"
include "eta.mm"
include "ceq2.mm"
include "a1i.mm"
include "mpbir.mm"
include "wim.mm"
include "weqi.mm"
include "wov.mm"
include "simpr.mm"
include "ax-cb1.mm"
include "ax-cb2.mm"
include "simpl.mm"
include "wct.mm"
include "beta.mm"
include "eqtri.mm"
include "mpbi.mm"
include "ex.mm"
include "wtru.mm"
include "adantl.mm"
include "alrimiv.mm"
include "ax5.mm"
include "mpd.mm"
include "syl.mm"

theorem ax11
  param hal: type al
  param vx: var x
  param vy: var y
  param ta: term A
  assume ax11.1: |- A : bool

  disjoint A x
  disjoint x y
  disjoint al x
  disjoint al y
  assert |- T. |= [ [ x : al = y : al ] ==> [ ( ! \ y : al . A ) ==> ( ! \ x : al . [ [ x : al = y : al ] ==> A ] ) ] ]

  proof
    kt
    hal
    vx
    tv
    #
    hal
    vy
    tv
    #
    ke
    kbr
    #
    tal
    hal
    vy
    ta
    kl
    #
    kc
    #
    tal
    hal
    vx
    @2
    ta
    tim
    kbr
    #
    kl
    #
    kc
    #
    tim
    kbr
    kt
    @2
    kct
    #
    @4
    @7
    @4
    @8
    @7
    @4
    tal
    hal
    vx
    @3
    @0
    kc
    #
    kl
    #
    kc
    #
    @7
    @4
    @11
    @4
    @4
    hal
    hb
    ht
    #
    hb
    tal
    @3
    hal
    wal
    #
    hal
    hb
    vy
    ta
    ax11.1
    wl
    #
    wc
    #
    id
    @11
    @4
    ke
    kbr
    #
    @4
    @15
    @12
    hb
    @10
    @3
    tal
    kt
    @13
    hal
    hb
    vx
    @9
    hal
    hb
    @3
    @0
    @14
    hal
    vx
    wv
    #
    wc
    #
    wl
    #
    hal
    hb
    vx
    @3
    @14
    eta
    ceq2
    #
    a1i
    mpbir
    @11
    @11
    @7
    @12
    hb
    tal
    @6
    @13
    hal
    hb
    vx
    @5
    hb
    hb
    hb
    @2
    ta
    tim
    wim
    hal
    @0
    @1
    @17
    hal
    vy
    wv
    weqi
    #
    ax11.1
    wov
    #
    wl
    wc
    #
    @11
    @12
    hb
    tal
    @10
    @13
    @19
    wc
    #
    id
    @11
    @7
    tim
    kbr
    #
    @11
    @24
    kt
    tal
    hal
    vx
    @9
    @5
    tim
    kbr
    #
    kl
    kc
    @25
    hb
    hb
    hb
    @11
    @7
    tim
    wim
    @11
    @2
    @4
    kct
    #
    @4
    @11
    @27
    @2
    @4
    @21
    @15
    simpr
    #
    @16
    @27
    @4
    @27
    @28
    ax-cb1
    @20
    a1i
    mpbir
    ax-cb2
    @23
    wov
    hal
    vx
    @26
    kt
    kt
    @9
    @5
    @9
    kt
    @5
    @9
    @2
    ta
    @9
    ta
    @9
    @2
    kct
    #
    @9
    @2
    @18
    @21
    simpl
    hb
    @9
    @3
    @1
    kc
    #
    ta
    @29
    @18
    hal
    hb
    @0
    @1
    @3
    @29
    @14
    @17
    @9
    @2
    @18
    @21
    simpr
    ceq2
    @30
    ta
    ke
    kbr
    @29
    @9
    @2
    @18
    @21
    wct
    hal
    hb
    vy
    ta
    ax11.1
    beta
    a1i
    eqtri
    mpbi
    ex
    wtru
    adantl
    ex
    alrimiv
    hal
    vx
    @9
    @5
    @18
    @22
    ax5
    mpd
    a1i
    mpd
    syl
    kt
    @2
    wtru
    @21
    wct
    adantl
    ex
    ex
end
