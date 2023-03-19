include "wi1.mm"
include "wa.mm"
include "wt.mm"
include "an1.mm"
include "ax-r1.mm"
include "u1lemle1.mm"
include "lan.mm"
include "ax-r2.mm"
include "bltr.mm"
include "3vded11.mm"

theorem 3vded13
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume 3vded13.1: |- ( b ^ ( c ->1 a ) ) =< ( c ->1 ( b ->1 a ) )
  assume 3vded13.2: |- c =< a


  assert |- c =< ( b ->1 a )

  proof
    wva
    wvb
    wvc
    wvb
    wvb
    wvc
    wva
    wi1
    #
    wa
    #
    wvc
    wvb
    wva
    wi1
    wi1
    wvb
    wvb
    wt
    wa
    #
    @1
    @2
    wvb
    wvb
    an1
    ax-r1
    wt
    @0
    wvb
    @0
    wt
    wvc
    wva
    3vded13.2
    u1lemle1
    ax-r1
    lan
    ax-r2
    3vded13.1
    bltr
    3vded11
end
