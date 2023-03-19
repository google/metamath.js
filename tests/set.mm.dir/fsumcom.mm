include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "wa.mm"
include "wb.mm"
include "ancom.mm"
include "a1i.mm"
include "fsumcom2.mm"

theorem fsumcom
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  assume fsumcom.1: |- ( ph -> A e. Fin )
  assume fsumcom.2: |- ( ph -> B e. Fin )
  assume fsumcom.3: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. CC )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> sum_ j e. A sum_ k e. B C = sum_ k e. B sum_ j e. A C )

  proof
    wph
    cA
    cB
    cB
    cA
    vj
    vk
    cC
    fsumcom.1
    fsumcom.2
    wph
    cB
    cfn
    wcel
    vj
    cv
    cA
    wcel
    #
    fsumcom.2
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
    fsumcom.3
    fsumcom2
end
