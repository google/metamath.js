include "u1lem9b.mm"

theorem lem4.6.3le2
  param wva: term a
  param wvb: term b


  assert |- a ' =< ( a ->1 b )

  proof
    wva
    wvb
    u1lem9b
end
