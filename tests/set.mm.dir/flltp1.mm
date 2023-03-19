include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "fllelt.mm"
include "simprd.mm"

theorem flltp1
  let cA: class A


  assert |- ( A e. RR -> A < ( ( |_ ` A ) + 1 ) )

  proof
    cA
    cr
    wcel
    cA
    cfl
    cfv
    #
    cA
    cle
    wbr
    cA
    @0
    c1
    caddc
    co
    clt
    wbr
    cA
    fllelt
    simprd
end
