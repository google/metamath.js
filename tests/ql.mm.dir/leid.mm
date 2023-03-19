include "id.mm"
include "bile.mm"

theorem leid
  let wva: term a


  assert |- a =< a

  proof
    wva
    wva
    wva
    id
    bile
end
