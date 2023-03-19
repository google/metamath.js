include "wceq.mm"
include "cif.mm"
include "ifeq1.mm"
include "ifeq2.mm"
include "sylan9eq.mm"

theorem ifeq12
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ C = D ) -> if ( ph , A , C ) = if ( ph , B , D ) )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    wph
    cA
    cC
    cif
    wph
    cB
    cC
    cif
    wph
    cB
    cD
    cif
    wph
    cA
    cB
    cC
    ifeq1
    wph
    cC
    cD
    cB
    ifeq2
    sylan9eq
end
