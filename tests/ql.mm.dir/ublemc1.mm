include "combi.mm"

theorem ublemc1
  param wva: term a
  param wvb: term b


  assert |- a C ( a == b )

  proof
    wva
    wvb
    combi
end
