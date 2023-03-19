include "cif.mm"
include "wcel.mm"
include "eleq2.mm"
include "elimif.mm"

theorem elif
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. if ( ph , B , C ) <-> ( ( ph /\ A e. B ) \/ ( -. ph /\ A e. C ) ) )

  proof
    wph
    cA
    wph
    cB
    cC
    cif
    #
    wcel
    cA
    cB
    wcel
    cA
    cC
    wcel
    cB
    cC
    @0
    cB
    cA
    eleq2
    @0
    cC
    cA
    eleq2
    elimif
end
