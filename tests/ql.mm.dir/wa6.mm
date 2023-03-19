include "tb.mm"
include "wn.mm"
include "wo.mm"
include "df-b.mm"
include "bi1.mm"

theorem wa6
  let wva: term a
  let wvb: term b


  assert |- ( ( a == b ) == ( ( a ' v b ' ) ' v ( a v b ) ' ) ) = 1

  proof
    wva
    wvb
    tb
    wva
    wn
    wvb
    wn
    wo
    wn
    wva
    wvb
    wo
    wn
    wo
    wva
    wvb
    df-b
    bi1
end
