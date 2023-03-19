include "wceq.mm"
include "cdif.mm"
include "difeq2.mm"
include "syl.mm"

theorem difeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume difeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C \ A ) = ( C \ B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cdif
    cC
    cB
    cdif
    wceq
    difeq1d.1
    cA
    cB
    cC
    difeq2
    syl
end
