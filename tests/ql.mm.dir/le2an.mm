include "wa.mm"
include "leran.mm"
include "lelan.mm"
include "letr.mm"

theorem le2an
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume le2.1: |- a =< b
  assume le2.2: |- c =< d


  assert |- ( a ^ c ) =< ( b ^ d )

  proof
    wva
    wvc
    wa
    wvb
    wvc
    wa
    wvb
    wvd
    wa
    wva
    wvb
    wvc
    le2.1
    leran
    wvc
    wvd
    wvb
    le2.2
    lelan
    letr
end
