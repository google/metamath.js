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
include "fsumf1o.mm"

theorem fsumshft
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let vm: setvar m
  assume fsumrev.1: |- ( ph -> K e. ZZ )
  assume fsumrev.2: |- ( ph -> M e. ZZ )
  assume fsumrev.3: |- ( ph -> N e. ZZ )
  assume fsumrev.4: |- ( ( ph /\ j e. ( M ... N ) ) -> A e. CC )
  assume fsumshft.5: |- ( j = ( k - K ) -> A = B )

  disjoint A k
  disjoint B j
  disjoint j k
  disjoint K j
  disjoint K k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint j ph
  disjoint k ph
  disjoint k m
  disjoint A m
  disjoint j m
  disjoint K m
  disjoint M m
  disjoint N m
  disjoint m ph
  assert |- ( ph -> sum_ j e. ( M ... N ) A = sum_ k e. ( ( M + K ) ... ( N + K ) ) B )

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
    fsumshft.5
    wph
    @0
    @1
    fzfid
    wph
    vj
    cK
    cM
    cN
    fsumrev.1
    fsumrev.2
    fsumrev.3
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
    fsumrev.4
    fsumf1o
end
