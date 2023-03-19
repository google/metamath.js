include "biid.mm"

theorem ska1
  let wva: term a


  assert |- ( a == a ) = 1

  proof
    wva
    biid
end
