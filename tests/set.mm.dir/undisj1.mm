include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cun.mm"
include "un00.mm"
include "indir.mm"
include "eqeq1i.mm"
include "bitr4i.mm"

theorem undisj1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A i^i C ) = (/) /\ ( B i^i C ) = (/) ) <-> ( ( A u. B ) i^i C ) = (/) )

  proof
    cA
    cC
    cin
    #
    c0
    wceq
    cB
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
    cun
    cC
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
    indir
    eqeq1i
    bitr4i
end
