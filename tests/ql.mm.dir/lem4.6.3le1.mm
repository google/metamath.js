include "u1lem9a.mm"

theorem lem4.6.3le1
  param wva: term a
  param wvb: term b


  assert |- ( a ' ->1 b ) ' =< a '

  proof
    wva
    wvb
    u1lem9a
end
