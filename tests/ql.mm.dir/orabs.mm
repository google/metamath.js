include "wa.mm"
include "wo.mm"
include "wn.mm"
include "df-a.mm"
include "lor.mm"
include "ax-a5.mm"
include "ax-r2.mm"

theorem orabs
  let wva: term a
  let wvb: term b


  assert |- ( a v ( a ^ b ) ) = a

  proof
    wva
    wva
    wvb
    wa
    #
    wo
    wva
    wva
    wn
    wvb
    wn
    #
    wo
    wn
    #
    wo
    wva
    @0
    @2
    wva
    wva
    wvb
    df-a
    lor
    wva
    @1
    ax-a5
    ax-r2
end
