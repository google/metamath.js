include "cif.mm"
include "wceq.mm"
include "eqeq2.mm"
include "elimif.mm"

theorem eqif
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = if ( ph , B , C ) <-> ( ( ph /\ A = B ) \/ ( -. ph /\ A = C ) ) )

  proof
    wph
    cA
    wph
    cB
    cC
    cif
    #
    wceq
    cA
    cB
    wceq
    cA
    cC
    wceq
    cB
    cC
    @0
    cB
    cA
    eqeq2
    @0
    cC
    cA
    eqeq2
    elimif
end
