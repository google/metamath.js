include "wn.mm"
include "wa.mm"
include "wo.mm"
include "i3lem1.mm"
include "ax-r1.mm"
include "df-c1.mm"
include "comcom2.mm"
include "comcom5.mm"

theorem i3lem2
  let wva: term a
  let wvb: term b
  assume i3lem.1: |- ( a ->3 b ) = 1


  assert |- a C b

  proof
    wva
    wvb
    wva
    wn
    #
    wvb
    @0
    wvb
    @0
    wvb
    wa
    @0
    wvb
    wn
    wa
    wo
    @0
    wva
    wvb
    i3lem.1
    i3lem1
    ax-r1
    df-c1
    comcom2
    comcom5
end
