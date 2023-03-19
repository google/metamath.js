include "combi.mm"

theorem ublemc1
  let wva: term a
  let wvb: term b


  assert |- a C ( a == b )

  proof
    wva
    wvb
    combi
end
