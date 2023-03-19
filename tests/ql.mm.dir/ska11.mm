include "woml.mm"

theorem ska11
  param wva: term a
  param wvb: term b


  assert |- ( ( a v ( a ' ^ ( a v b ) ) ) == ( a v b ) ) = 1

  proof
    wva
    wvb
    woml
end
