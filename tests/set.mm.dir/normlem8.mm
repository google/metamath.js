include "cva.mm"
include "co.mm"
include "csp.mm"
include "caddc.mm"
include "chil.mm"
include "wcel.mm"
include "wceq.mm"
include "his7.mm"
include "mp3an.mm"
include "oveq12i.mm"
include "hvaddcli.mm"
include "ax-his2.mm"
include "hicli.mm"
include "add42i.mm"
include "3eqtr4i.mm"

theorem normlem8
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume normlem8.1: |- A e. ~H
  assume normlem8.2: |- B e. ~H
  assume normlem8.3: |- C e. ~H
  assume normlem8.4: |- D e. ~H


  assert |- ( ( A +h B ) .ih ( C +h D ) ) = ( ( ( A .ih C ) + ( B .ih D ) ) + ( ( A .ih D ) + ( B .ih C ) ) )

  proof
    cA
    cC
    cD
    cva
    co
    #
    csp
    co
    #
    cB
    @0
    csp
    co
    #
    caddc
    co
    #
    cA
    cC
    csp
    co
    #
    cA
    cD
    csp
    co
    #
    caddc
    co
    #
    cB
    cC
    csp
    co
    #
    cB
    cD
    csp
    co
    #
    caddc
    co
    #
    caddc
    co
    cA
    cB
    cva
    co
    @0
    csp
    co
    #
    @4
    @8
    caddc
    co
    @5
    @7
    caddc
    co
    caddc
    co
    @1
    @6
    @2
    @9
    caddc
    cA
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    cD
    chil
    wcel
    #
    @1
    @6
    wceq
    normlem8.1
    normlem8.3
    normlem8.4
    cA
    cC
    cD
    his7
    mp3an
    cB
    chil
    wcel
    #
    @12
    @13
    @2
    @9
    wceq
    normlem8.2
    normlem8.3
    normlem8.4
    cB
    cC
    cD
    his7
    mp3an
    oveq12i
    @11
    @14
    @0
    chil
    wcel
    @10
    @3
    wceq
    normlem8.1
    normlem8.2
    cC
    cD
    normlem8.3
    normlem8.4
    hvaddcli
    cA
    cB
    @0
    ax-his2
    mp3an
    @4
    @8
    @5
    @7
    cA
    cC
    normlem8.1
    normlem8.3
    hicli
    cB
    cD
    normlem8.2
    normlem8.4
    hicli
    cA
    cD
    normlem8.1
    normlem8.4
    hicli
    cB
    cC
    normlem8.2
    normlem8.3
    hicli
    add42i
    3eqtr4i
end
