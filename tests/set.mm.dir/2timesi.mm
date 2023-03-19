include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "2times.mm"
include "ax-mp.mm"

theorem 2timesi
  let cA: class A
  assume 2timesi.1: |- A e. CC


  assert |- ( 2 x. A ) = ( A + A )

  proof
    cA
    cc
    wcel
    c2
    cA
    cmul
    co
    cA
    cA
    caddc
    co
    wceq
    2timesi.1
    cA
    2times
    ax-mp
end
