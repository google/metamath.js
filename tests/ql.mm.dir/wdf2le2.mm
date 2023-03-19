include "wdf-le2.mm"
include "wleoa.mm"

theorem wdf2le2
  param wva: term a
  param wvb: term b
  assume wdf2le2.1: |- ( a =<2 b ) = 1


  assert |- ( ( a ^ b ) == a ) = 1

  proof
    wva
    wvb
    wvb
    wva
    wvb
    wdf2le2.1
    wdf-le2
    wleoa
end
