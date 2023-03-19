include "csu.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "reccld.mm"
include "isummulc1.mm"
include "isumcl.mm"
include "divrecd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"

theorem isumdivc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  assume isumcl.1: |- Z = ( ZZ>= ` M )
  assume isumcl.2: |- ( ph -> M e. ZZ )
  assume isumcl.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumcl.4: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume isumcl.5: |- ( ph -> seq M ( + , F ) e. dom ~~> )
  assume summulc.6: |- ( ph -> B e. CC )
  assume isumdivc.7: |- ( ph -> B =/= 0 )

  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint Z k
  disjoint M k
  disjoint A m
  disjoint k m
  disjoint B m
  disjoint F m
  disjoint m ph
  disjoint Z m
  disjoint M m
  assert |- ( ph -> ( sum_ k e. Z A / B ) = sum_ k e. Z ( A / B ) )

  proof
    wph
    cZ
    cA
    vk
    csu
    #
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    cZ
    cA
    @1
    cmul
    co
    #
    vk
    csu
    @0
    cB
    cdiv
    co
    cZ
    cA
    cB
    cdiv
    co
    #
    vk
    csu
    wph
    cA
    @1
    vk
    cF
    cM
    cZ
    isumcl.1
    isumcl.2
    isumcl.3
    isumcl.4
    isumcl.5
    wph
    cB
    summulc.6
    isumdivc.7
    reccld
    isummulc1
    wph
    @0
    cB
    wph
    cA
    vk
    cF
    cM
    cZ
    isumcl.1
    isumcl.2
    isumcl.3
    isumcl.4
    isumcl.5
    isumcl
    summulc.6
    isumdivc.7
    divrecd
    wph
    cZ
    @3
    @2
    vk
    wph
    vk
    cv
    cZ
    wcel
    #
    wa
    cA
    cB
    isumcl.4
    wph
    cB
    cc
    wcel
    @4
    summulc.6
    adantr
    wph
    cB
    cc0
    wne
    @4
    isumdivc.7
    adantr
    divrecd
    sumeq2dv
    3eqtr4d
end
