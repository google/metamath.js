include "cfz.mm"
include "co.mm"
include "cmin.mm"
include "csu.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "fzval3.mm"
include "syl.mm"
include "sumeq1d.mm"
include "telfsumo2.mm"
include "eqtrd.mm"

theorem telfsum2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cM: class M
  let cN: class N
  assume telfsum.1: |- ( k = j -> A = B )
  assume telfsum.2: |- ( k = ( j + 1 ) -> A = C )
  assume telfsum.3: |- ( k = M -> A = D )
  assume telfsum.4: |- ( k = ( N + 1 ) -> A = E )
  assume telfsum.5: |- ( ph -> N e. ZZ )
  assume telfsum.6: |- ( ph -> ( N + 1 ) e. ( ZZ>= ` M ) )
  assume telfsum.7: |- ( ( ph /\ k e. ( M ... ( N + 1 ) ) ) -> A e. CC )

  disjoint A j
  disjoint B k
  disjoint C k
  disjoint j k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint j ph
  disjoint k ph
  disjoint D k
  disjoint E k
  assert |- ( ph -> sum_ j e. ( M ... N ) ( C - B ) = ( E - D ) )

  proof
    wph
    cM
    cN
    cfz
    co
    #
    cC
    cB
    cmin
    co
    #
    vj
    csu
    cM
    cN
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @1
    vj
    csu
    cE
    cD
    cmin
    co
    wph
    @0
    @3
    @1
    vj
    wph
    cN
    cz
    wcel
    @0
    @3
    wceq
    telfsum.5
    cM
    cN
    fzval3
    syl
    sumeq1d
    wph
    cA
    cB
    cC
    cD
    vj
    vk
    cE
    cM
    @2
    telfsum.1
    telfsum.2
    telfsum.3
    telfsum.4
    telfsum.6
    telfsum.7
    telfsumo2
    eqtrd
end
