include "id.mm"
include "bile.mm"

theorem leid
  param wva: term a


  assert |- a =< a

  proof
    wva
    wva
    wva
    id
    bile
end
