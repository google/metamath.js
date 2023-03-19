include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "csb.mm"
include "cprod.mm"
include "cmul.mm"
include "cc.mm"
include "wcel.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "weq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "csbeq1.mm"
include "fprodp1.mm"
include "nfcv.mm"
include "cbvprodi.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"

theorem fprodp1s
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vm: setvar m
  assume fprodp1s.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fprodp1s.2: |- ( ( ph /\ k e. ( M ... ( N + 1 ) ) ) -> A e. CC )

  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint A m
  disjoint k m
  disjoint m ph
  disjoint M m
  disjoint N m
  assert |- ( ph -> prod_ k e. ( M ... ( N + 1 ) ) A = ( prod_ k e. ( M ... N ) A x. [_ ( N + 1 ) / k ]_ A ) )

  proof
    wph
    cM
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    vk
    vm
    cv
    #
    cA
    csb
    #
    vm
    cprod
    cM
    cN
    cfz
    co
    #
    @3
    vm
    cprod
    #
    vk
    @0
    cA
    csb
    #
    cmul
    co
    @1
    cA
    vk
    cprod
    @4
    cA
    vk
    cprod
    #
    @6
    cmul
    co
    wph
    @3
    @6
    vm
    cM
    cN
    fprodp1s.1
    wph
    cA
    cc
    wcel
    #
    vk
    @1
    wral
    @2
    @1
    wcel
    @3
    cc
    wcel
    #
    wph
    @8
    vk
    @1
    fprodp1s.2
    ralrimiva
    @8
    @9
    vk
    @2
    @1
    vk
    @3
    cc
    vk
    @2
    cA
    nfcsb1v
    #
    nfel1
    vk
    vm
    weq
    cA
    @3
    cc
    vk
    @2
    cA
    csbeq1a
    #
    eleq1d
    rspc
    mpan9
    vk
    @2
    @0
    cA
    csbeq1
    fprodp1
    @1
    cA
    @3
    vk
    vm
    vm
    cA
    nfcv
    #
    @10
    @11
    cbvprodi
    @7
    @5
    @6
    cmul
    @4
    cA
    @3
    vk
    vm
    @12
    @10
    @11
    cbvprodi
    oveq1i
    3eqtr4g
end
