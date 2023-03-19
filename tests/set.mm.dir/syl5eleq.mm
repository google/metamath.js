include "wcel.mm"
include "a1i.mm"
include "eleqtrd.mm"

theorem syl5eleq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5eleq.1: |- A e. B
  assume syl5eleq.2: |- ( ph -> B = C )


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cB
    cC
    cA
    cB
    wcel
    wph
    syl5eleq.1
    a1i
    syl5eleq.2
    eleqtrd
end
