include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cun.mm"
include "un00.mm"
include "indi.mm"
include "eqeq1i.mm"
include "bitr4i.mm"

theorem undisj2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A i^i B ) = (/) /\ ( A i^i C ) = (/) ) <-> ( A i^i ( B u. C ) ) = (/) )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    cA
    cC
    cin
    #
    c0
    wceq
    wa
    @0
    @1
    cun
    #
    c0
    wceq
    cA
    cB
    cC
    cun
    cin
    #
    c0
    wceq
    @0
    @1
    un00
    @3
    @2
    c0
    cA
    cB
    cC
    indi
    eqeq1i
    bitr4i
end
