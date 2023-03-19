include "wa.mm"
include "wo.mm"
include "ledio.mm"
include "ax-a2.mm"
include "2an.mm"
include "le3tr1.mm"

theorem ledior
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( b ^ c ) v a ) =< ( ( b v a ) ^ ( c v a ) )

  proof
    wva
    wvb
    wvc
    wa
    #
    wo
    wva
    wvb
    wo
    #
    wva
    wvc
    wo
    #
    wa
    @0
    wva
    wo
    wvb
    wva
    wo
    #
    wvc
    wva
    wo
    #
    wa
    wva
    wvb
    wvc
    ledio
    @0
    wva
    ax-a2
    @3
    @1
    @4
    @2
    wvb
    wva
    ax-a2
    wvc
    wva
    ax-a2
    2an
    le3tr1
end
