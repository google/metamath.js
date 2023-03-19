include "wi3.mm"
include "wt.mm"
include "i31.mm"
include "li3.mm"
include "bi1.mm"
include "wwbmpr.mm"

theorem i3aa
  param wva: term a
  param wvb: term b
  assume i3aa.1: |- a = 1


  assert |- ( b ->3 a ) = 1

  proof
    wvb
    wva
    wi3
    #
    wvb
    wt
    wi3
    #
    wvb
    i31
    @0
    @1
    wva
    wt
    wvb
    i3aa.1
    li3
    bi1
    wwbmpr
end
