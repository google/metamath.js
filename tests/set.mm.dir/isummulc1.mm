include "csu.mm"
include "cmul.mm"
include "co.mm"
include "isummulc2.mm"
include "isumcl.mm"
include "mulcomd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "adantr.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"

theorem isummulc1
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
  assert |- ( ph -> ( sum_ k e. Z A x. B ) = sum_ k e. Z ( A x. B ) )

  proof
    wph
    cB
    cZ
    cA
    vk
    csu
    #
    cmul
    co
    cZ
    cB
    cA
    cmul
    co
    #
    vk
    csu
    @0
    cB
    cmul
    co
    cZ
    cA
    cB
    cmul
    co
    #
    vk
    csu
    wph
    cA
    cB
    vk
    cF
    cM
    cZ
    isumcl.1
    isumcl.2
    isumcl.3
    isumcl.4
    isumcl.5
    summulc.6
    isummulc2
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
    mulcomd
    wph
    cZ
    @2
    @1
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
    @3
    summulc.6
    adantr
    mulcomd
    sumeq2dv
    3eqtr4d
end
