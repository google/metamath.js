include "wcmtr.mm"
include "wt.mm"
include "cmtrcom.mm"
include "ax-r2.mm"

theorem wcomcom
  let wva: term a
  let wvb: term b
  assume wcomcom.1: |- C ( a , b ) = 1


  assert |- C ( b , a ) = 1

  proof
    wvb
    wva
    wcmtr
    wva
    wvb
    wcmtr
    wt
    wvb
    wva
    cmtrcom
    wcomcom.1
    ax-r2
end
