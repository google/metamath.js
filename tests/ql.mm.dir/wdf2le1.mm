include "wleao.mm"
include "wdf-le1.mm"

theorem wdf2le1
  let wva: term a
  let wvb: term b
  assume wdf2le1.1: |- ( ( a ^ b ) == a ) = 1


  assert |- ( a =<2 b ) = 1

  proof
    wva
    wvb
    wva
    wvb
    wva
    wdf2le1.1
    wleao
    wdf-le1
end
