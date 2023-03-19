include "i3bi.mm"

theorem u3lembi
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->3 b ) ^ ( b ->3 a ) ) = ( a == b )

  proof
    wva
    wvb
    i3bi
end
