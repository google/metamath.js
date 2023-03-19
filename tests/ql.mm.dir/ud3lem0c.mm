include "ni31.mm"

theorem ud3lem0c
  param wva: term a
  param wvb: term b


  assert |- ( a ->3 b ) ' = ( ( ( a v b ' ) ^ ( a v b ) ) ^ ( a ' v ( a ^ b ' ) ) )

  proof
    wva
    wvb
    ni31
end
