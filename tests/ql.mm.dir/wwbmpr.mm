include "wr1.mm"
include "wwbmp.mm"

theorem wwbmpr
  param wva: term a
  param wvb: term b
  assume wwbmpr.1: |- b = 1
  assume wwbmpr.2: |- ( a == b ) = 1


  assert |- a = 1

  proof
    wvb
    wva
    wwbmpr.1
    wva
    wvb
    wwbmpr.2
    wr1
    wwbmp
end
