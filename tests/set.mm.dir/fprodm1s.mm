include "cfz.mm"
include "co.mm"
include "cv.mm"
include "csb.mm"
include "cprod.mm"
include "c1.mm"
include "cmin.mm"
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
include "fprodm1.mm"
include "nfcv.mm"
include "cbvprodi.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"

theorem fprodm1s
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vm: setvar m
  assume fprodm1s.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fprodm1s.2: |- ( ( ph /\ k e. ( M ... N ) ) -> A e. CC )

  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint A m
  disjoint k m
  disjoint m ph
  disjoint M m
  disjoint N m
  assert |- ( ph -> prod_ k e. ( M ... N ) A = ( prod_ k e. ( M ... ( N - 1 ) ) A x. [_ N / k ]_ A ) )

  proof
    wph
    cM
    cN
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
    c1
    cmin
    co
    cfz
    co
    #
    @2
    vm
    cprod
    #
    vk
    cN
    cA
    csb
    #
    cmul
    co
    @0
    cA
    vk
    cprod
    @3
    cA
    vk
    cprod
    #
    @5
    cmul
    co
    wph
    @2
    @5
    vm
    cM
    cN
    fprodm1s.1
    wph
    cA
    cc
    wcel
    #
    vk
    @0
    wral
    @1
    @0
    wcel
    @2
    cc
    wcel
    #
    wph
    @7
    vk
    @0
    fprodm1s.2
    ralrimiva
    @7
    @8
    vk
    @1
    @0
    vk
    @2
    cc
    vk
    @1
    cA
    nfcsb1v
    #
    nfel1
    vk
    vm
    weq
    cA
    @2
    cc
    vk
    @1
    cA
    csbeq1a
    #
    eleq1d
    rspc
    mpan9
    vk
    @1
    cN
    cA
    csbeq1
    fprodm1
    @0
    cA
    @2
    vk
    vm
    vm
    cA
    nfcv
    #
    @9
    @10
    cbvprodi
    @6
    @4
    @5
    cmul
    @3
    cA
    @2
    vk
    vm
    @11
    @9
    @10
    cbvprodi
    oveq1i
    3eqtr4g
end
