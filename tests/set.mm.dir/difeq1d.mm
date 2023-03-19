include "wceq.mm"
include "cdif.mm"
include "difeq1.mm"
include "syl.mm"

theorem difeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume difeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A \ C ) = ( B \ C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cdif
    cB
    cC
    cdif
    wceq
    difeq1d.1
    cA
    cB
    cC
    difeq1
    syl
end
