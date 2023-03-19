include "wcel.mm"
include "cif.mm"
include "eleq1.mm"
include "ifboth.mm"

theorem ifcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. C /\ B e. C ) -> if ( ph , A , B ) e. C )

  proof
    wph
    cA
    cC
    wcel
    cB
    cC
    wcel
    wph
    cA
    cB
    cif
    #
    cC
    wcel
    cA
    cB
    cA
    @0
    cC
    eleq1
    cB
    @0
    cC
    eleq1
    ifboth
end
