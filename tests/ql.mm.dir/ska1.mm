include "biid.mm"

theorem ska1
  param wva: term a


  assert |- ( a == a ) = 1

  proof
    wva
    biid
end
