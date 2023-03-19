include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "crest.mm"
include "co.mm"
include "cuni.mm"
include "wss.mm"
include "wceq.mm"
include "simpl.mm"
include "inss2.mm"
include "restuni.mm"
include "sylancl.mm"
include "restin.mm"
include "unieqd.mm"
include "eqtr4d.mm"

theorem restuni2
  let cA: class A
  let cJ: class J
  let cV: class V
  let cX: class X
  assume restin.1: |- X = U. J


  assert |- ( ( J e. Top /\ A e. V ) -> ( A i^i X ) = U. ( J |`t A ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cA
    cX
    cin
    #
    cJ
    @3
    crest
    co
    #
    cuni
    #
    cJ
    cA
    crest
    co
    #
    cuni
    @2
    @0
    @3
    cX
    wss
    @3
    @5
    wceq
    @0
    @1
    simpl
    cA
    cX
    inss2
    @3
    cJ
    cX
    restin.1
    restuni
    sylancl
    @2
    @6
    @4
    cA
    cJ
    ctop
    cV
    cX
    restin.1
    restin
    unieqd
    eqtr4d
end
