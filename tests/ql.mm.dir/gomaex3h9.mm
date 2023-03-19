include "wn.mm"
include "leid.mm"
include "ax-r4.mm"
include "le3tr1.mm"

theorem gomaex3h9
  let wvq: term q
  let wvw: term w
  let wvx: term x
  assume gomaex3h9.20: |- w = q '
  assume gomaex3h9.21: |- x = q


  assert |- w =< x '

  proof
    wvq
    wn
    #
    @0
    wvw
    wvx
    wn
    @0
    leid
    gomaex3h9.20
    wvx
    wvq
    gomaex3h9.21
    ax-r4
    le3tr1
end
