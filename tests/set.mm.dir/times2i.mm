include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "times2.mm"
include "ax-mp.mm"

theorem times2i
  let cA: class A
  assume 2timesi.1: |- A e. CC


  assert |- ( A x. 2 ) = ( A + A )

  proof
    cA
    cc
    wcel
    cA
    c2
    cmul
    co
    cA
    cA
    caddc
    co
    wceq
    2timesi.1
    cA
    times2
    ax-mp
end
