include "wn.mm"
include "ax-r4.mm"
include "le3tr1.mm"

theorem gomaex3h2
  let wvb: term b
  let wvc: term c
  let wvh: term h
  let wvi: term i
  assume gomaex3h2.2: |- b =< c '
  assume gomaex3h2.13: |- h = b
  assume gomaex3h2.14: |- i = c


  assert |- h =< i '

  proof
    wvb
    wvc
    wn
    wvh
    wvi
    wn
    gomaex3h2.2
    gomaex3h2.13
    wvi
    wvc
    gomaex3h2.14
    ax-r4
    le3tr1
end
