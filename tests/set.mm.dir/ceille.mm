include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cceil.mm"
include "cfv.mm"
include "cneg.mm"
include "cfl.mm"
include "wceq.mm"
include "ceilval.mm"
include "3ad2ant1.mm"
include "ceile.mm"
include "eqbrtrd.mm"

theorem ceille
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. ZZ /\ A <_ B ) -> ( |^ ` A ) <_ B )

  proof
    cA
    cr
    wcel
    #
    cB
    cz
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    cA
    cceil
    cfv
    #
    cA
    cneg
    cfl
    cfv
    cneg
    #
    cB
    cle
    @0
    @1
    @3
    @4
    wceq
    @2
    cA
    ceilval
    3ad2ant1
    cA
    cB
    ceile
    eqbrtrd
end
