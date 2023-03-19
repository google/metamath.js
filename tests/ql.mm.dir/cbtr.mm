include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-c2.mm"
include "lan.mm"
include "ax-r4.mm"
include "2or.mm"
include "ax-r2.mm"
include "df-c1.mm"

theorem cbtr
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume cbtr.1: |- a C b
  assume cbtr.2: |- b = c


  assert |- a C c

  proof
    wva
    wvc
    wva
    wva
    wvb
    wa
    #
    wva
    wvb
    wn
    #
    wa
    #
    wo
    wva
    wvc
    wa
    #
    wva
    wvc
    wn
    #
    wa
    #
    wo
    wva
    wvb
    cbtr.1
    df-c2
    @0
    @3
    @2
    @5
    wvb
    wvc
    wva
    cbtr.2
    lan
    @1
    @4
    wva
    wvb
    wvc
    cbtr.2
    ax-r4
    lan
    2or
    ax-r2
    df-c1
end
