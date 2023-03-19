include "wa.mm"
include "tb.mm"
include "wt.mm"
include "ancom.mm"
include "2bi.mm"
include "wran.mm"
include "ax-r2.mm"

theorem wlan
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume wlan.1: |- ( a == b ) = 1


  assert |- ( ( c ^ a ) == ( c ^ b ) ) = 1

  proof
    wvc
    wva
    wa
    #
    wvc
    wvb
    wa
    #
    tb
    wva
    wvc
    wa
    #
    wvb
    wvc
    wa
    #
    tb
    wt
    @0
    @2
    @1
    @3
    wvc
    wva
    ancom
    wvc
    wvb
    ancom
    2bi
    wva
    wvb
    wvc
    wlan.1
    wran
    ax-r2
end
