include "wceq.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "3bitr4g.mm"

theorem eqeq2d
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  assume eqeq2d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C = A <-> C = B ) )

  proof
    wph
    cA
    cC
    wceq
    cB
    cC
    wceq
    cC
    cA
    wceq
    cC
    cB
    wceq
    wph
    cA
    cB
    cC
    eqeq2d.1
    eqeq1d
    cC
    cA
    eqcom
    cC
    cB
    eqcom
    3bitr4g
end
