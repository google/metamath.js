include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "negid.mm"
include "ax-mp.mm"

theorem negidi
  let cA: class A
  assume negidi.1: |- A e. CC


  assert |- ( A + -u A ) = 0

  proof
    cA
    cc
    wcel
    cA
    cA
    cneg
    caddc
    co
    cc0
    wceq
    negidi.1
    cA
    negid
    ax-mp
end
