include "woml.mm"

theorem ska11
  let wva: term a
  let wvb: term b


  assert |- ( ( a v ( a ' ^ ( a v b ) ) ) == ( a v b ) ) = 1

  proof
    wva
    wvb
    woml
end
