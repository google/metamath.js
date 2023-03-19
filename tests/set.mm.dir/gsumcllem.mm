include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "feqmptd.mm"
include "adantr.mm"
include "wcel.mm"
include "cdif.mm"
include "difeq2.mm"
include "dif0.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "suppssr.mm"
include "sylan2.mm"
include "anassrs.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"

theorem gsumcllem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume gsumcllem.f: |- ( ph -> F : A --> B )
  assume gsumcllem.a: |- ( ph -> A e. V )
  assume gsumcllem.z: |- ( ph -> Z e. U )
  assume gsumcllem.s: |- ( ph -> ( F supp Z ) C_ W )

  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint W k
  assert |- ( ( ph /\ W = (/) ) -> F = ( k e. A |-> Z ) )

  proof
    wph
    cW
    c0
    wceq
    #
    wa
    #
    cF
    vk
    cA
    vk
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    vk
    cA
    cZ
    cmpt
    wph
    cF
    @4
    wceq
    @0
    wph
    vk
    cA
    cB
    cF
    gsumcllem.f
    feqmptd
    adantr
    @1
    vk
    cA
    @3
    cZ
    wph
    @0
    @2
    cA
    wcel
    #
    @3
    cZ
    wceq
    #
    @0
    @5
    wa
    wph
    @2
    cA
    cW
    cdif
    #
    wcel
    #
    @6
    @0
    @8
    @5
    @0
    @7
    cA
    @2
    @0
    @7
    cA
    c0
    cdif
    cA
    cW
    c0
    cA
    difeq2
    cA
    dif0
    syl6eq
    eleq2d
    biimpar
    wph
    cA
    cB
    cU
    cF
    cV
    cW
    @2
    cZ
    gsumcllem.f
    gsumcllem.s
    gsumcllem.a
    gsumcllem.z
    suppssr
    sylan2
    anassrs
    mpteq2dva
    eqtrd
end
