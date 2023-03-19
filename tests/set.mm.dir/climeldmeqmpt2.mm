include "cmpt.mm"
include "cvv.mm"
include "nfmpt1.mm"
include "mptexd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "sselda.mm"
include "fvmpt4.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "climeldmeqf.mm"

theorem climeldmeqmpt2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vk: setvar k
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume climeldmeqmpt2.k: |- F/ k ph
  assume climeldmeqmpt2.m: |- ( ph -> M e. ZZ )
  assume climeldmeqmpt2.z: |- Z = ( ZZ>= ` M )
  assume climeldmeqmpt2.a: |- ( ph -> A e. W )
  assume climeldmeqmpt2.t: |- ( ph -> B e. V )
  assume climeldmeqmpt2.i: |- ( ph -> Z C_ A )
  assume climeldmeqmpt2.l: |- ( ph -> Z C_ B )
  assume climeldmeqmpt2.b: |- ( ( ph /\ k e. Z ) -> C e. U )

  disjoint A k
  disjoint B k
  disjoint Z k
  assert |- ( ph -> ( ( k e. A |-> C ) e. dom ~~> <-> ( k e. B |-> C ) e. dom ~~> ) )

  proof
    wph
    vk
    vk
    cA
    cC
    cmpt
    #
    vk
    cB
    cC
    cmpt
    #
    cM
    cvv
    cvv
    cZ
    climeldmeqmpt2.k
    vk
    cA
    cC
    nfmpt1
    vk
    cB
    cC
    nfmpt1
    climeldmeqmpt2.z
    wph
    vk
    cA
    cC
    cW
    climeldmeqmpt2.a
    mptexd
    wph
    vk
    cB
    cC
    cV
    climeldmeqmpt2.t
    mptexd
    climeldmeqmpt2.m
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    #
    @2
    @0
    cfv
    #
    cC
    @2
    @1
    cfv
    #
    @3
    @2
    cA
    wcel
    cC
    cU
    wcel
    #
    @4
    cC
    wceq
    wph
    cZ
    cA
    @2
    climeldmeqmpt2.i
    sselda
    climeldmeqmpt2.b
    vk
    cA
    cC
    cU
    fvmpt4
    syl2anc
    @3
    @2
    cB
    wcel
    @6
    @5
    cC
    wceq
    wph
    cZ
    cB
    @2
    climeldmeqmpt2.l
    sselda
    climeldmeqmpt2.b
    vk
    cB
    cC
    cU
    fvmpt4
    syl2anc
    eqtr4d
    climeldmeqf
end
