include "wo.mm"
include "wa.mm"
include "id.mm"
include "bile.mm"
include "ler2an.mm"
include "letr.mm"

theorem str
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume str.1: |- a =< ( b v c )
  assume str.2: |- ( a ^ ( b v c ) ) =< b


  assert |- a =< b

  proof
    wva
    wva
    wvb
    wvc
    wo
    #
    wa
    wvb
    wva
    wva
    @0
    wva
    wva
    wva
    id
    bile
    str.1
    ler2an
    str.2
    letr
end
