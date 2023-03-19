include "i3bi.mm"

theorem u3lembi
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->3 b ) ^ ( b ->3 a ) ) = ( a == b )

  proof
    wva
    wvb
    i3bi
end
