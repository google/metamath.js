include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cfl.mm"
include "cfz.mm"
include "cppi.mm"
include "ppisval.mm"
include "fveq2d.mm"
include "ppival.mm"
include "cz.mm"
include "wceq.mm"
include "flcl.mm"
include "ppival2.mm"
include "syl.mm"
include "3eqtr4rd.mm"

theorem ppifl
  let cA: class A


  assert |- ( A e. RR -> ( ppi ` ( |_ ` A ) ) = ( ppi ` A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cicc
    co
    cprime
    cin
    #
    chash
    cfv
    c2
    cA
    cfl
    cfv
    #
    cfz
    co
    cprime
    cin
    #
    chash
    cfv
    #
    cA
    cppi
    cfv
    @2
    cppi
    cfv
    #
    @0
    @1
    @3
    chash
    cA
    ppisval
    fveq2d
    cA
    ppival
    @0
    @2
    cz
    wcel
    @5
    @4
    wceq
    cA
    flcl
    @2
    ppival2
    syl
    3eqtr4rd
end
