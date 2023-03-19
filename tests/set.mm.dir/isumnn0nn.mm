include "cn0.mm"
include "csu.mm"
include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cn.mm"
include "nn0uz.mm"
include "0zd.mm"
include "isum1p.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "0nn0.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "0p1e1.mm"
include "fveq2i.mm"
include "nnuz.mm"
include "eqtr4i.mm"
include "sumeq1i.mm"
include "a1i.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem isumnn0nn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  assume isumnn0nn.1: |- ( k = 0 -> A = B )
  assume isumnn0nn.2: |- ( ( ph /\ k e. NN0 ) -> ( F ` k ) = A )
  assume isumnn0nn.3: |- ( ( ph /\ k e. NN0 ) -> A e. CC )
  assume isumnn0nn.4: |- ( ph -> seq 0 ( + , F ) e. dom ~~> )

  disjoint F k
  disjoint B k
  disjoint k ph
  assert |- ( ph -> sum_ k e. NN0 A = ( B + sum_ k e. NN A ) )

  proof
    wph
    cn0
    cA
    vk
    csu
    cc0
    cF
    cfv
    #
    cc0
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cA
    vk
    csu
    #
    caddc
    co
    cB
    cn
    cA
    vk
    csu
    #
    caddc
    co
    wph
    cA
    vk
    cF
    cc0
    cn0
    nn0uz
    wph
    0zd
    isumnn0nn.2
    isumnn0nn.3
    isumnn0nn.4
    isum1p
    wph
    @0
    cB
    @3
    @4
    caddc
    cc0
    cn0
    wcel
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cA
    wceq
    #
    vk
    cn0
    wral
    @0
    cB
    wceq
    #
    0nn0
    wph
    @7
    vk
    cn0
    isumnn0nn.2
    ralrimiva
    @7
    @8
    vk
    cc0
    cn0
    @5
    cc0
    wceq
    @6
    @0
    cA
    cB
    @5
    cc0
    cF
    fveq2
    isumnn0nn.1
    eqeq12d
    rspcv
    mpsyl
    @3
    @4
    wceq
    wph
    @2
    cn
    cA
    vk
    @2
    c1
    cuz
    cfv
    cn
    @1
    c1
    cuz
    0p1e1
    fveq2i
    nnuz
    eqtr4i
    sumeq1i
    a1i
    oveq12d
    eqtrd
end
