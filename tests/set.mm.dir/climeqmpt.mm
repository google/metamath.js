include "cmpt.mm"
include "cvv.mm"
include "nfmpt1.mm"
include "mptexd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "climeqf.mm"

theorem climeqmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume climeqmpt.x: |- F/ x ph
  assume climeqmpt.a: |- ( ph -> A e. V )
  assume climeqmpt.b: |- ( ph -> B e. W )
  assume climeqmpt.m: |- ( ph -> M e. ZZ )
  assume climeqmpt.z: |- Z = ( ZZ>= ` M )
  assume climeqmpt.s: |- ( ph -> Z C_ A )
  assume climeqmpt.t: |- ( ph -> Z C_ B )
  assume climeqmpt.c: |- ( ( ph /\ x e. Z ) -> C e. U )

  disjoint A x
  disjoint B x
  disjoint Z x
  assert |- ( ph -> ( ( x e. A |-> C ) ~~> D <-> ( x e. B |-> C ) ~~> D ) )

  proof
    wph
    cD
    vx
    vx
    cA
    cC
    cmpt
    #
    vx
    cB
    cC
    cmpt
    #
    cM
    cvv
    cvv
    cZ
    climeqmpt.x
    vx
    cA
    cC
    nfmpt1
    vx
    cB
    cC
    nfmpt1
    climeqmpt.m
    climeqmpt.z
    wph
    vx
    cA
    cC
    cV
    climeqmpt.a
    mptexd
    wph
    vx
    cB
    cC
    cW
    climeqmpt.b
    mptexd
    wph
    vx
    cv
    #
    cZ
    wcel
    #
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
    @4
    @2
    cA
    wcel
    cC
    cU
    wcel
    #
    @5
    cC
    wceq
    @4
    cZ
    cA
    @2
    wph
    cZ
    cA
    wss
    @3
    climeqmpt.s
    adantr
    wph
    @3
    simpr
    #
    sseldd
    climeqmpt.c
    vx
    cA
    cC
    cU
    @0
    @0
    eqid
    fvmpt2
    syl2anc
    @4
    @6
    cC
    @4
    @2
    cB
    wcel
    @7
    @6
    cC
    wceq
    @4
    cZ
    cB
    @2
    wph
    cZ
    cB
    wss
    @3
    climeqmpt.t
    adantr
    @8
    sseldd
    climeqmpt.c
    vx
    cB
    cC
    cU
    @1
    @1
    eqid
    fvmpt2
    syl2anc
    eqcomd
    eqtrd
    climeqf
end
