include "letrd.mm"

theorem int-ineqtransd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume int-ineqtransd.1: |- ( ph -> A e. RR )
  assume int-ineqtransd.2: |- ( ph -> B e. RR )
  assume int-ineqtransd.3: |- ( ph -> C e. RR )
  assume int-ineqtransd.4: |- ( ph -> B <_ A )
  assume int-ineqtransd.5: |- ( ph -> C <_ B )


  assert |- ( ph -> C <_ A )

  proof
    wph
    cC
    cB
    cA
    int-ineqtransd.3
    int-ineqtransd.2
    int-ineqtransd.1
    int-ineqtransd.5
    int-ineqtransd.4
    letrd
end
