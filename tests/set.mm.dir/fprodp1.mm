include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cprod.mm"
include "cmin.mm"
include "cmul.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "peano2uz.mm"
include "syl.mm"
include "fprodm1.mm"
include "cz.mm"
include "eluzelz.mm"
include "zcnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "oveq2d.mm"
include "prodeq1d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem fprodp1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume fprodp1.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fprodp1.2: |- ( ( ph /\ k e. ( M ... ( N + 1 ) ) ) -> A e. CC )
  assume fprodp1.3: |- ( k = ( N + 1 ) -> A = B )

  disjoint B k
  disjoint k ph
  disjoint M k
  disjoint N k
  assert |- ( ph -> prod_ k e. ( M ... ( N + 1 ) ) A = ( prod_ k e. ( M ... N ) A x. B ) )

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
    cA
    vk
    cprod
    cM
    @0
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vk
    cprod
    #
    cB
    cmul
    co
    cM
    cN
    cfz
    co
    #
    cA
    vk
    cprod
    #
    cB
    cmul
    co
    wph
    cA
    cB
    vk
    cM
    @0
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @0
    @6
    wcel
    fprodp1.1
    cM
    cN
    peano2uz
    syl
    fprodp1.2
    fprodp1.3
    fprodm1
    wph
    @3
    @5
    cB
    cmul
    wph
    @2
    @4
    cA
    vk
    wph
    @1
    cN
    cM
    cfz
    wph
    cN
    c1
    wph
    cN
    wph
    @7
    cN
    cz
    wcel
    fprodp1.1
    cM
    cN
    eluzelz
    syl
    zcnd
    wph
    1cnd
    pncand
    oveq2d
    prodeq1d
    oveq1d
    eqtrd
end
