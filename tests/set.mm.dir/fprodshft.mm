include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "fzfid.mm"
include "mptfzshft.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "oveq1.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "fprodf1o.mm"

theorem fprodshft
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  assume fprodshft.1: |- ( ph -> K e. ZZ )
  assume fprodshft.2: |- ( ph -> M e. ZZ )
  assume fprodshft.3: |- ( ph -> N e. ZZ )
  assume fprodshft.4: |- ( ( ph /\ j e. ( M ... N ) ) -> A e. CC )
  assume fprodshft.5: |- ( j = ( k - K ) -> A = B )

  disjoint A k
  disjoint B j
  disjoint j k
  disjoint j ph
  disjoint K j
  disjoint K k
  disjoint k ph
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  assert |- ( ph -> prod_ j e. ( M ... N ) A = prod_ k e. ( ( M + K ) ... ( N + K ) ) B )

  proof
    wph
    cM
    cN
    cfz
    co
    cA
    cM
    cK
    caddc
    co
    #
    cN
    cK
    caddc
    co
    #
    cfz
    co
    #
    cB
    vj
    vk
    vj
    @2
    vj
    cv
    #
    cK
    cmin
    co
    #
    cmpt
    #
    vk
    cv
    #
    cK
    cmin
    co
    #
    fprodshft.5
    wph
    @0
    @1
    fzfid
    wph
    vj
    cK
    cM
    cN
    fprodshft.1
    fprodshft.2
    fprodshft.3
    mptfzshft
    @6
    @2
    wcel
    @6
    @5
    cfv
    @7
    wceq
    wph
    vj
    @6
    @4
    @7
    @2
    @5
    @3
    @6
    cK
    cmin
    oveq1
    @5
    eqid
    @6
    cK
    cmin
    ovex
    fvmpt
    adantl
    fprodshft.4
    fprodf1o
end
