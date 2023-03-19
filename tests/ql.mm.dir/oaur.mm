include "wi1.mm"
include "wo.mm"
include "wa.mm"
include "leid.mm"
include "lel2or.mm"
include "lelan.mm"
include "ancom.mm"
include "u1lemaa.mm"
include "ax-r2.mm"
include "lbtr.mm"
include "lear.mm"
include "letr.mm"

theorem oaur
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume oaur.1: |- b =< ( a ->1 c )


  assert |- ( a ^ ( ( a ->1 c ) v b ) ) =< c

  proof
    wva
    wva
    wvc
    wi1
    #
    wvb
    wo
    #
    wa
    #
    wva
    wvc
    wa
    #
    wvc
    @2
    wva
    @0
    wa
    #
    @3
    @1
    @0
    wva
    @0
    @0
    wvb
    @0
    leid
    oaur.1
    lel2or
    lelan
    @4
    @0
    wva
    wa
    @3
    wva
    @0
    ancom
    wva
    wvc
    u1lemaa
    ax-r2
    lbtr
    wva
    wvc
    lear
    letr
end
