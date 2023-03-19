include "kt.mm"
include "ke.mm"
include "kbr.mm"
include "kc.mm"
include "tim.mm"
include "kct.mm"
include "wtru.mm"
include "weqi.mm"
include "wct.mm"
include "hb.mm"
include "wc.mm"
include "simpr.mm"
include "ceq2.mm"
include "adantr.mm"
include "mpbi.mm"
include "ex.mm"

theorem ax13
  param hal: type al
  param ta: term A
  param tb: term B
  param tc: term C
  assume ax13.1: |- A : al
  assume ax13.2: |- B : al
  assume ax13.3: |- C : ( al -> bool )


  assert |- T. |= [ [ A = B ] ==> [ ( C A ) ==> ( C B ) ] ]

  proof
    kt
    ta
    tb
    ke
    kbr
    #
    tc
    ta
    kc
    #
    tc
    tb
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
    ta
    tb
    ax13.1
    ax13.2
    weqi
    #
    wct
    hal
    hb
    tc
    ta
    ax13.3
    ax13.1
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
    ta
    tb
    tc
    @3
    ax13.3
    ax13.1
    kt
    @0
    wtru
    @4
    simpr
    ceq2
    @5
    adantr
    mpbi
    ex
    ex
end
