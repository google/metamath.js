include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wdf-c2.mm"
include "wlan.mm"
include "wr4.mm"
include "w2or.mm"
include "wr2.mm"
include "wdf-c1.mm"

theorem wcbtr
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume wcbtr.1: |- C ( a , b ) = 1
  assume wcbtr.2: |- ( b == c ) = 1


  assert |- C ( a , c ) = 1

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
    wcbtr.1
    wdf-c2
    @0
    @3
    @2
    @5
    wvb
    wvc
    wva
    wcbtr.2
    wlan
    @1
    @4
    wva
    wvb
    wvc
    wcbtr.2
    wr4
    wlan
    w2or
    wr2
    wdf-c1
end
