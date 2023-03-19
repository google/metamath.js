include "csu.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cfn.mm"
include "wcel.mm"
include "adantr.mm"
include "fsum2d.mm"
include "iunxpconst.mm"
include "sumeq1i.mm"
include "syl6eq.mm"

theorem fsumxp
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  assume fsumxp.1: |- ( z = <. j , k >. -> D = C )
  assume fsumxp.2: |- ( ph -> A e. Fin )
  assume fsumxp.3: |- ( ph -> B e. Fin )
  assume fsumxp.4: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. CC )

  disjoint j k
  disjoint j z
  disjoint A j
  disjoint k z
  disjoint A k
  disjoint A z
  disjoint B j
  disjoint B k
  disjoint B z
  disjoint C z
  disjoint D j
  disjoint D k
  disjoint j ph
  disjoint k ph
  disjoint ph z
  assert |- ( ph -> sum_ j e. A sum_ k e. B C = sum_ z e. ( A X. B ) D )

  proof
    wph
    cA
    cB
    cC
    vk
    csu
    vj
    csu
    vj
    cA
    vj
    cv
    #
    csn
    cB
    cxp
    ciun
    #
    cD
    vz
    csu
    cA
    cB
    cxp
    #
    cD
    vz
    csu
    wph
    vz
    cA
    cB
    cC
    cD
    vj
    vk
    fsumxp.1
    fsumxp.2
    wph
    cB
    cfn
    wcel
    @0
    cA
    wcel
    fsumxp.3
    adantr
    fsumxp.4
    fsum2d
    @1
    @2
    cD
    vz
    vj
    cA
    cB
    iunxpconst
    sumeq1i
    syl6eq
end
