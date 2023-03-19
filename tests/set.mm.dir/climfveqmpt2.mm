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
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "climfveqf.mm"

theorem climfveqmpt2
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
  assume climfveqmpt2.k: |- F/ k ph
  assume climfveqmpt2.m: |- ( ph -> M e. ZZ )
  assume climfveqmpt2.z: |- Z = ( ZZ>= ` M )
  assume climfveqmpt2.a: |- ( ph -> A e. V )
  assume climfveqmpt2.c: |- ( ph -> B e. W )
  assume climfveqmpt2.s: |- ( ph -> Z C_ A )
  assume climfveqmpt2.i: |- ( ph -> Z C_ B )
  assume climfveqmpt2.b: |- ( ( ph /\ k e. Z ) -> C e. U )

  disjoint A k
  disjoint B k
  disjoint Z k
  assert |- ( ph -> ( ~~> ` ( k e. A |-> C ) ) = ( ~~> ` ( k e. B |-> C ) ) )

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
    climfveqmpt2.k
    vk
    cA
    cC
    nfmpt1
    vk
    cB
    cC
    nfmpt1
    climfveqmpt2.z
    wph
    vk
    cA
    cC
    cV
    climfveqmpt2.a
    mptexd
    wph
    vk
    cB
    cC
    cW
    climfveqmpt2.c
    mptexd
    climfveqmpt2.m
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
    climfveqmpt2.s
    sselda
    climfveqmpt2.b
    vk
    cA
    cC
    cU
    @0
    @0
    eqid
    fvmpt2
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
    climfveqmpt2.i
    sselda
    climfveqmpt2.b
    vk
    cB
    cC
    cU
    @1
    @1
    eqid
    fvmpt2
    syl2anc
    eqtr4d
    climfveqf
end
