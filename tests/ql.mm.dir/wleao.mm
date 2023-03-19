include "wo.mm"
include "wa.mm"
include "wa2.mm"
include "wr1.mm"
include "wancom.mm"
include "wr2.mm"
include "wlor.mm"
include "wa5b.mm"

theorem wleao
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume wleao.1: |- ( ( c ^ b ) == a ) = 1


  assert |- ( ( a v b ) == b ) = 1

  proof
    wva
    wvb
    wo
    #
    wvb
    wvb
    wvc
    wa
    #
    wo
    #
    wvb
    @0
    wvb
    wva
    wo
    @2
    wva
    wvb
    wa2
    wva
    @1
    wvb
    wva
    wvc
    wvb
    wa
    #
    @1
    @3
    wva
    wleao.1
    wr1
    @1
    @3
    wvb
    wvc
    wancom
    wr1
    wr2
    wlor
    wr2
    wvb
    wvc
    wa5b
    wr2
end
