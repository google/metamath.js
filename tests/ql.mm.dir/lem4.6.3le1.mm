include "u1lem9a.mm"

theorem lem4.6.3le1
  let wva: term a
  let wvb: term b


  assert |- ( a ' ->1 b ) ' =< a '

  proof
    wva
    wvb
    u1lem9a
end
