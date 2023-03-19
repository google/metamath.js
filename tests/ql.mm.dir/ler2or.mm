include "wo.mm"
include "oridm.mm"
include "ax-r1.mm"
include "le2or.mm"
include "bltr.mm"

theorem ler2or
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume ler2.1: |- a =< b
  assume ler2.2: |- a =< c


  assert |- a =< ( b v c )

  proof
    wva
    wva
    wva
    wo
    #
    wvb
    wvc
    wo
    @0
    wva
    wva
    oridm
    ax-r1
    wva
    wvb
    wva
    wvc
    ler2.1
    ler2.2
    le2or
    bltr
end
