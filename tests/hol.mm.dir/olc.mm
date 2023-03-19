include "hb.mm"
include "tv.mm"
include "tim.mm"
include "kbr.mm"
include "kl.mm"
include "kt.mm"
include "ke.mm"
include "tor.mm"
include "wim.mm"
include "wv.mm"
include "wov.mm"
include "wtru.mm"
include "kct.mm"
include "simpl.mm"
include "simpr.mm"
include "mpd.mm"
include "ex.mm"
include "adantr.mm"
include "eqtru.mm"
include "eqcomi.mm"
include "leq.mm"
include "tal.mm"
include "kc.mm"
include "wor.mm"
include "orval.mm"
include "wl.mm"
include "alval.mm"
include "eqtri.mm"
include "a1i.mm"
include "mpbir.mm"

theorem olc
  param ta: term A
  param tb: term B
  let vx: var x
  assume olc.1: |- A : bool
  assume olc.2: |- B : bool


  assert |- B |= [ A \/ B ]

  proof
    hb
    vx
    ta
    hb
    vx
    tv
    #
    tim
    kbr
    #
    tb
    @0
    tim
    kbr
    #
    @0
    tim
    kbr
    #
    tim
    kbr
    #
    kl
    #
    hb
    vx
    kt
    kl
    ke
    kbr
    #
    ta
    tb
    tor
    kbr
    #
    tb
    hb
    hb
    vx
    @4
    kt
    tb
    hb
    hb
    hb
    @1
    @3
    tim
    wim
    hb
    hb
    hb
    ta
    @0
    tim
    wim
    olc.1
    hb
    vx
    wv
    #
    wov
    #
    hb
    hb
    hb
    @2
    @0
    tim
    wim
    hb
    hb
    hb
    tb
    @0
    tim
    wim
    olc.2
    @8
    wov
    #
    @8
    wov
    wov
    #
    hb
    kt
    @4
    tb
    wtru
    @4
    tb
    tb
    @1
    @3
    tb
    @1
    @3
    tb
    @2
    @0
    tb
    @2
    kct
    tb
    @0
    @8
    tb
    @2
    olc.2
    @10
    simpl
    tb
    @2
    olc.2
    @10
    simpr
    mpd
    ex
    @9
    adantr
    ex
    eqtru
    eqcomi
    leq
    @7
    @6
    ke
    kbr
    tb
    olc.2
    hb
    @7
    tal
    @5
    kc
    @6
    kt
    hb
    hb
    hb
    ta
    tb
    tor
    wor
    olc.1
    olc.2
    wov
    vx
    ta
    tb
    olc.1
    olc.2
    orval
    hb
    vx
    @5
    hb
    hb
    vx
    @4
    @11
    wl
    alval
    eqtri
    a1i
    mpbir
end
