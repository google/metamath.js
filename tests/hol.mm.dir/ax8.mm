include "kt.mm"
include "ke.mm"
include "kbr.mm"
include "tim.mm"
include "kct.mm"
include "weqi.mm"
include "simpl.mm"
include "eqcomi.mm"
include "simpr.mm"
include "eqtri.mm"
include "ex.mm"
include "wtru.mm"
include "adantl.mm"

theorem ax8
  param hal: type al
  param ta: term A
  param tb: term B
  param tc: term C
  assume ax8.1: |- A : al
  assume ax8.2: |- B : al
  assume ax8.3: |- C : al


  assert |- T. |= [ [ A = B ] ==> [ [ A = C ] ==> [ B = C ] ] ]

  proof
    kt
    ta
    tb
    ke
    kbr
    #
    ta
    tc
    ke
    kbr
    #
    tb
    tc
    ke
    kbr
    #
    tim
    kbr
    #
    @0
    kt
    @3
    @0
    @1
    @2
    hal
    tb
    ta
    tc
    @0
    @1
    kct
    #
    ax8.2
    hal
    ta
    tb
    @4
    ax8.1
    @0
    @1
    hal
    ta
    tb
    ax8.1
    ax8.2
    weqi
    #
    hal
    ta
    tc
    ax8.1
    ax8.3
    weqi
    #
    simpl
    eqcomi
    @0
    @1
    @5
    @6
    simpr
    eqtri
    ex
    wtru
    adantl
    ex
end
