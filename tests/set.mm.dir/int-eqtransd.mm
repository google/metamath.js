include "eqtrd.mm"

theorem int-eqtransd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume int-eqtransd.1: |- ( ph -> A = B )
  assume int-eqtransd.2: |- ( ph -> B = C )


  assert |- ( ph -> A = C )

  proof
    wph
    cA
    cB
    cC
    int-eqtransd.1
    int-eqtransd.2
    eqtrd
end
