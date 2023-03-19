include "wn.mm"
include "wo.mm"
include "wa.mm"
include "binr1.mm"
include "i3ror.mm"
include "df-a.mm"
include "i33tr1.mm"

theorem i3ran
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume i3ran.1: |- ( a ->3 b ) = 1


  assert |- ( ( a ^ c ) ->3 ( b ^ c ) ) = 1

  proof
    wva
    wn
    #
    wvc
    wn
    #
    wo
    #
    wn
    wvb
    wn
    #
    @1
    wo
    #
    wn
    wva
    wvc
    wa
    wvb
    wvc
    wa
    @4
    @2
    @3
    @0
    @1
    wva
    wvb
    i3ran.1
    binr1
    i3ror
    binr1
    wva
    wvc
    df-a
    wvb
    wvc
    df-a
    i33tr1
end
