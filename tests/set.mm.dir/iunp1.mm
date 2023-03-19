include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "ciun.mm"
include "csn.mm"
include "cun.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "fzsuc.mm"
include "syl.mm"
include "iuneq1d.mm"
include "iunxun.mm"
include "a1i.mm"
include "ovex.mm"
include "iunxsnf.mm"
include "uneq2d.mm"
include "3eqtrd.mm"

theorem iunp1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cN: class N
  assume iunp1.1: |- F/_ k B
  assume iunp1.2: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume iunp1.3: |- ( k = ( N + 1 ) -> A = B )

  disjoint M k
  disjoint N k
  assert |- ( ph -> U_ k e. ( M ... ( N + 1 ) ) A = ( U_ k e. ( M ... N ) A u. B ) )

  proof
    wph
    vk
    cM
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    cA
    ciun
    vk
    cM
    cN
    cfz
    co
    #
    @0
    csn
    #
    cun
    #
    cA
    ciun
    #
    vk
    @2
    cA
    ciun
    #
    vk
    @3
    cA
    ciun
    #
    cun
    #
    @6
    cB
    cun
    wph
    vk
    @1
    @4
    cA
    wph
    cN
    cM
    cuz
    cfv
    wcel
    @1
    @4
    wceq
    iunp1.2
    cM
    cN
    fzsuc
    syl
    iuneq1d
    @5
    @8
    wceq
    wph
    vk
    @2
    @3
    cA
    iunxun
    a1i
    wph
    @7
    cB
    @6
    @7
    cB
    wceq
    wph
    vk
    @0
    cA
    cB
    iunp1.1
    cN
    c1
    caddc
    ovex
    iunp1.3
    iunxsnf
    a1i
    uneq2d
    3eqtrd
end
