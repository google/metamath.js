include "wo.mm"
include "wa.mm"
include "leo.mm"
include "ler2an.mm"
include "leor.mm"
include "leran.mm"
include "lel2or.mm"
include "ax-ml.mm"
include "lebi.mm"

theorem ml
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( a v ( b ^ ( a v c ) ) ) = ( ( a v b ) ^ ( a v c ) )

  proof
    wva
    wvb
    wva
    wvc
    wo
    #
    wa
    #
    wo
    wva
    wvb
    wo
    #
    @0
    wa
    #
    wva
    @3
    @1
    wva
    @2
    @0
    wva
    wvb
    leo
    wva
    wvc
    leo
    ler2an
    wvb
    @2
    @0
    wvb
    wva
    leor
    leran
    lel2or
    wva
    wvb
    wvc
    ax-ml
    lebi
end
