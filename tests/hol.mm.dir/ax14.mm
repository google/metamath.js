include "kt.mm"
include "ke.mm"
include "kbr.mm"
include "kc.mm"
include "tim.mm"
include "kct.mm"
include "wtru.mm"
include "hb.mm"
include "ht.mm"
include "weqi.mm"
include "wct.mm"
include "wc.mm"
include "simpr.mm"
include "ceq1.mm"
include "adantr.mm"
include "mpbi.mm"
include "ex.mm"

theorem ax14
  let hal: type al
  let ta: term A
  let tb: term B
  let tc: term C
  assume ax14.1: |- A : ( al -> bool )
  assume ax14.2: |- B : ( al -> bool )
  assume ax14.3: |- C : al


  assert |- T. |= [ [ A = B ] ==> [ ( A C ) ==> ( B C ) ] ]

  proof
    kt
    ta
    tb
    ke
    kbr
    #
    ta
    tc
    kc
    #
    tb
    tc
    kc
    #
    tim
    kbr
    kt
    @0
    kct
    #
    @1
    @2
    @1
    @2
    @3
    @1
    kct
    @3
    @1
    kt
    @0
    wtru
    hal
    hb
    ht
    ta
    tb
    ax14.1
    ax14.2
    weqi
    #
    wct
    hal
    hb
    ta
    tc
    ax14.1
    ax14.3
    wc
    #
    simpr
    @3
    @1
    @1
    @2
    ke
    kbr
    hal
    hb
    tc
    ta
    @3
    tb
    ax14.1
    ax14.3
    kt
    @0
    wtru
    @4
    simpr
    ceq1
    @5
    adantr
    mpbi
    ex
    ex
end
