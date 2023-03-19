include "nfcv.mm"
include "esumsnf.mm"

theorem esumsn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cV: class V
  assume esumsn.1: |- ( ( ph /\ k = M ) -> A = B )
  assume esumsn.2: |- ( ph -> M e. V )
  assume esumsn.3: |- ( ph -> B e. ( 0 [,] +oo ) )

  disjoint B k
  disjoint M k
  disjoint V k
  disjoint k ph
  assert |- ( ph -> sum* k e. { M } A = B )

  proof
    wph
    cA
    cB
    vk
    cM
    cV
    vk
    cB
    nfcv
    esumsn.1
    esumsn.2
    esumsn.3
    esumsnf
end
