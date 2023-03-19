include "wcel.mm"
include "eleq2i.mm"
include "sylbi.mm"

theorem eleq2s
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eleq2s.1: |- ( A e. B -> ph )
  assume eleq2s.2: |- C = B


  assert |- ( A e. C -> ph )

  proof
    cA
    cC
    wcel
    cA
    cB
    wcel
    wph
    cC
    cB
    cA
    eleq2s.2
    eleq2i
    eleq2s.1
    sylbi
end
