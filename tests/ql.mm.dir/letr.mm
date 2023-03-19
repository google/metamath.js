include "wa.mm"
include "wo.mm"
include "df-le2.mm"
include "ax-r5.mm"
include "ax-r1.mm"
include "ax-a3.mm"
include "3tr2.mm"
include "lan.mm"
include "anabs.mm"
include "ax-r2.mm"
include "df2le1.mm"

theorem letr
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume letr.1: |- a =< b
  assume letr.2: |- b =< c


  assert |- a =< c

  proof
    wva
    wvc
    wva
    wvc
    wa
    wva
    wva
    wvb
    wvc
    wo
    #
    wo
    #
    wa
    wva
    wvc
    @1
    wva
    @0
    wva
    wvb
    wo
    #
    wvc
    wo
    #
    wvc
    @1
    @3
    @0
    @2
    wvb
    wvc
    wva
    wvb
    letr.1
    df-le2
    ax-r5
    ax-r1
    wvb
    wvc
    letr.2
    df-le2
    wva
    wvb
    wvc
    ax-a3
    3tr2
    lan
    wva
    @0
    anabs
    ax-r2
    df2le1
end
