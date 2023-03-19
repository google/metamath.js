include "cif.mm"
include "wcel.mm"
include "eleq1.mm"
include "elimif.mm"

theorem ifel
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( if ( ph , A , B ) e. C <-> ( ( ph /\ A e. C ) \/ ( -. ph /\ B e. C ) ) )

  proof
    wph
    wph
    cA
    cB
    cif
    #
    cC
    wcel
    cA
    cC
    wcel
    cB
    cC
    wcel
    cA
    cB
    @0
    cA
    cC
    eleq1
    @0
    cB
    cC
    eleq1
    elimif
end
