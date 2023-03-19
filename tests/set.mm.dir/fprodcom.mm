include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "wa.mm"
include "wb.mm"
include "ancom.mm"
include "a1i.mm"
include "fprodcom2.mm"

theorem fprodcom
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  assume fprodcom.1: |- ( ph -> A e. Fin )
  assume fprodcom.2: |- ( ph -> B e. Fin )
  assume fprodcom.3: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. CC )

  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint j k
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> prod_ j e. A prod_ k e. B C = prod_ k e. B prod_ j e. A C )

  proof
    wph
    cA
    cB
    cB
    cA
    vj
    vk
    cC
    fprodcom.1
    fprodcom.2
    wph
    cB
    cfn
    wcel
    vj
    cv
    cA
    wcel
    #
    fprodcom.2
    adantr
    @0
    vk
    cv
    cB
    wcel
    #
    wa
    @1
    @0
    wa
    wb
    wph
    @0
    @1
    ancom
    a1i
    fprodcom.3
    fprodcom2
end
