include "cun.mm"
include "cin.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "eqimss.mm"
include "unss.mm"
include "ssin.mm"
include "sstr.mm"
include "sylbir.mm"
include "simpl.mm"
include "anim12i.mm"
include "syl.mm"
include "eqss.mm"
include "sylibr.mm"
include "unidm.mm"
include "inidm.mm"
include "eqtr4i.mm"
include "uneq2.mm"
include "ineq2.mm"
include "3eqtr3a.mm"
include "impbii.mm"

theorem uneqin
  let cA: class A
  let cB: class B


  assert |- ( ( A u. B ) = ( A i^i B ) <-> A = B )

  proof
    cA
    cB
    cun
    #
    cA
    cB
    cin
    #
    wceq
    #
    cA
    cB
    wceq
    #
    @2
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wa
    #
    @3
    @2
    @0
    @1
    wss
    #
    @6
    @0
    @1
    eqimss
    @7
    cA
    @1
    wss
    #
    cB
    @1
    wss
    #
    wa
    @6
    cA
    cB
    @1
    unss
    @8
    @4
    @9
    @5
    @8
    cA
    cA
    wss
    @4
    wa
    @4
    cA
    cA
    cB
    ssin
    cA
    cA
    cB
    sstr
    sylbir
    @9
    @5
    cB
    cB
    wss
    #
    wa
    @5
    cB
    cA
    cB
    ssin
    @5
    @10
    simpl
    sylbir
    anim12i
    sylbir
    syl
    cA
    cB
    eqss
    sylibr
    @3
    cA
    cA
    cun
    #
    cA
    cA
    cin
    #
    @0
    @1
    @11
    cA
    @12
    cA
    unidm
    cA
    inidm
    eqtr4i
    cA
    cB
    cA
    uneq2
    cA
    cB
    cA
    ineq2
    3eqtr3a
    impbii
end
