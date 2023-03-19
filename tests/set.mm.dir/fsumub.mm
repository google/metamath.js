include "csu.mm"
include "cle.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "rpred.mm"
include "rpge0d.mm"
include "fsumge1.mm"
include "breqtrd.mm"

theorem fsumub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cK: class K
  assume fsumub.1: |- ( k = K -> B = D )
  assume fsumub.2: |- ( ph -> A e. Fin )
  assume fsumub.3: |- ( ph -> sum_ k e. A B = C )
  assume fsumub.4: |- ( ( ph /\ k e. A ) -> B e. RR+ )
  assume fsumub.k: |- ( ph -> K e. A )

  disjoint A k
  disjoint D k
  disjoint K k
  disjoint k ph
  assert |- ( ph -> D <_ C )

  proof
    wph
    cD
    cA
    cB
    vk
    csu
    cC
    cle
    wph
    cA
    cB
    cD
    vk
    cK
    fsumub.2
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    cB
    fsumub.4
    rpred
    @0
    cB
    fsumub.4
    rpge0d
    fsumub.1
    fsumub.k
    fsumge1
    fsumub.3
    breqtrd
end
