include "wi1.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "anor1.mm"
include "ax-r1.mm"
include "u1lemana.mm"
include "ax-r2.mm"
include "con1.mm"

theorem u1lemnoa
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->1 b ) ' v a ) = a

  proof
    wva
    wvb
    wi1
    #
    wn
    wva
    wo
    #
    wva
    @1
    wn
    #
    @0
    wva
    wn
    #
    wa
    #
    @3
    @4
    @2
    @0
    wva
    anor1
    ax-r1
    wva
    wvb
    u1lemana
    ax-r2
    con1
end
