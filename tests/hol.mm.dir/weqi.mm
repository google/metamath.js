include "hb.mm"
include "ke.mm"
include "weq.mm"
include "wov.mm"

theorem weqi
  let hal: type al
  let ta: term A
  let tb: term B
  assume weqi.1: |- A : al
  assume weqi.2: |- B : al


  assert |- [ A = B ] : bool

  proof
    hal
    hal
    hb
    ta
    tb
    ke
    hal
    weq
    weqi.1
    weqi.2
    wov
end
