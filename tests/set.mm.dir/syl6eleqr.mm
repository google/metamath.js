include "eqcomi.mm"
include "syl6eleq.mm"

theorem syl6eleqr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl6eleqr.1: |- ( ph -> A e. B )
  assume syl6eleqr.2: |- C = B


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cB
    cC
    syl6eleqr.1
    cC
    cB
    syl6eleqr.2
    eqcomi
    syl6eleq
end
