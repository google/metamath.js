include "cprod.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cfn.mm"
include "wcel.mm"
include "adantr.mm"
include "fprod2d.mm"
include "iunxpconst.mm"
include "prodeq1i.mm"
include "syl6eq.mm"

theorem fprodxp
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  assume fprodxp.1: |- ( z = <. j , k >. -> D = C )
  assume fprodxp.2: |- ( ph -> A e. Fin )
  assume fprodxp.3: |- ( ph -> B e. Fin )
  assume fprodxp.4: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. CC )

  disjoint A j
  disjoint A k
  disjoint A z
  disjoint B j
  disjoint B k
  disjoint B z
  disjoint C z
  disjoint D j
  disjoint D k
  disjoint j k
  disjoint j ph
  disjoint j z
  disjoint k ph
  disjoint k z
  disjoint ph z
  assert |- ( ph -> prod_ j e. A prod_ k e. B C = prod_ z e. ( A X. B ) D )

  proof
    wph
    cA
    cB
    cC
    vk
    cprod
    vj
    cprod
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
    cprod
    cA
    cB
    cxp
    #
    cD
    vz
    cprod
    wph
    vz
    cA
    cB
    cC
    cD
    vj
    vk
    fprodxp.1
    fprodxp.2
    wph
    cB
    cfn
    wcel
    @0
    cA
    wcel
    fprodxp.3
    adantr
    fprodxp.4
    fprod2d
    @1
    @2
    cD
    vz
    vj
    cA
    cB
    iunxpconst
    prodeq1i
    syl6eq
end
