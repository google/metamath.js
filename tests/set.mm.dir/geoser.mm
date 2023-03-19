include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "csu.mm"
include "cmin.mm"
include "c1.mm"
include "cdiv.mm"
include "cfz.mm"
include "cn0.mm"
include "wcel.mm"
include "0nn0.mm"
include "a1i.mm"
include "cuz.mm"
include "cfv.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "geoserg.mm"
include "cz.mm"
include "wceq.mm"
include "nn0zd.mm"
include "fzoval.mm"
include "syl.mm"
include "sumeq1d.mm"
include "exp0d.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"

theorem geoser
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cN: class N
  assume geoser.1: |- ( ph -> A e. CC )
  assume geoser.2: |- ( ph -> A =/= 1 )
  assume geoser.3: |- ( ph -> N e. NN0 )

  disjoint A k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> sum_ k e. ( 0 ... ( N - 1 ) ) ( A ^ k ) = ( ( 1 - ( A ^ N ) ) / ( 1 - A ) ) )

  proof
    wph
    cc0
    cN
    cfzo
    co
    #
    cA
    vk
    cv
    cexp
    co
    #
    vk
    csu
    cA
    cc0
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cmin
    co
    #
    c1
    cA
    cmin
    co
    #
    cdiv
    co
    cc0
    cN
    c1
    cmin
    co
    cfz
    co
    #
    @1
    vk
    csu
    c1
    @3
    cmin
    co
    #
    @5
    cdiv
    co
    wph
    cA
    vk
    cc0
    cN
    geoser.1
    geoser.2
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    wph
    cN
    cn0
    cc0
    cuz
    cfv
    geoser.3
    nn0uz
    syl6eleq
    geoserg
    wph
    @0
    @6
    @1
    vk
    wph
    cN
    cz
    wcel
    @0
    @6
    wceq
    wph
    cN
    geoser.3
    nn0zd
    cc0
    cN
    fzoval
    syl
    sumeq1d
    wph
    @4
    @7
    @5
    cdiv
    wph
    @2
    c1
    @3
    cmin
    wph
    cA
    geoser.1
    exp0d
    oveq1d
    oveq1d
    3eqtr3d
end
