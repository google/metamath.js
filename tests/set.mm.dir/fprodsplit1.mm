include "nfv.mm"
include "nfcvd.mm"
include "fprodsplit1f.mm"

theorem fprodsplit1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume fprodsplit1.a: |- ( ph -> A e. Fin )
  assume fprodsplit1.b: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fprodsplit1.c: |- ( ph -> C e. A )
  assume fprodsplit1.d: |- ( ( ph /\ k = C ) -> B = D )

  disjoint A k
  disjoint C k
  disjoint D k
  disjoint k ph
  assert |- ( ph -> prod_ k e. A B = ( D x. prod_ k e. ( A \ { C } ) B ) )

  proof
    wph
    cA
    cB
    cC
    cD
    vk
    wph
    vk
    nfv
    wph
    vk
    cD
    nfcvd
    fprodsplit1.a
    fprodsplit1.b
    fprodsplit1.c
    fprodsplit1.d
    fprodsplit1f
end
