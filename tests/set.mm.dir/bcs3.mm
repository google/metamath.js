include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "csp.mm"
include "co.mm"
include "cabs.mm"
include "wceq.mm"
include "abshicom.mm"
include "3adant3.mm"
include "bcs2.mm"
include "3com12.mm"
include "eqbrtrd.mm"

theorem bcs3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H /\ ( normh ` B ) <_ 1 ) -> ( abs ` ( A .ih B ) ) <_ ( normh ` A ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cB
    cno
    cfv
    c1
    cle
    wbr
    #
    w3a
    cA
    cB
    csp
    co
    cabs
    cfv
    #
    cB
    cA
    csp
    co
    cabs
    cfv
    #
    cA
    cno
    cfv
    #
    cle
    @0
    @1
    @3
    @4
    wceq
    @2
    cA
    cB
    abshicom
    3adant3
    @1
    @0
    @2
    @4
    @5
    cle
    wbr
    cB
    cA
    bcs2
    3com12
    eqbrtrd
end
