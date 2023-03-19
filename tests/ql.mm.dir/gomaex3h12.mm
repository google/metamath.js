include "wn.mm"
include "ax-r4.mm"
include "le3tr1.mm"

theorem gomaex3h12
  param wva: term a
  param wvf: term f
  param wvg: term g
  param wvz: term z
  assume gomaex3h12.6: |- f =< a '
  assume gomaex3h12.12: |- g = a
  assume gomaex3h12.23: |- z = f


  assert |- z =< g '

  proof
    wvf
    wva
    wn
    wvz
    wvg
    wn
    gomaex3h12.6
    gomaex3h12.23
    wvg
    wva
    gomaex3h12.12
    ax-r4
    le3tr1
end
