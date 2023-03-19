include "wceq.mm"
include "a1i.mm"
include "eleqtrd.mm"

theorem syl6eleq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl6eleq.1: |- ( ph -> A e. B )
  assume syl6eleq.2: |- B = C


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cB
    cC
    syl6eleq.1
    cB
    cC
    wceq
    wph
    syl6eleq.2
    a1i
    eleqtrd
end
