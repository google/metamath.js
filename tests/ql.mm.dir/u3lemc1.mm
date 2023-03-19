include "comi31.mm"

theorem u3lemc1
  param wva: term a
  param wvb: term b


  assert |- a C ( a ->3 b )

  proof
    wva
    wvb
    comi31
end
