include "csu.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "simpr.mm"
include "sumeq1d.mm"
include "sum0.mm"
include "syl6eq.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "cc.mm"
include "wss.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "adantlr.mm"
include "cfn.mm"
include "fsumcl2lem.mm"
include "pm2.61dane.mm"

theorem fsumcllem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  assume fsumcllem.1: |- ( ph -> S C_ CC )
  assume fsumcllem.2: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume fsumcllem.3: |- ( ph -> A e. Fin )
  assume fsumcllem.4: |- ( ( ph /\ k e. A ) -> B e. S )
  assume fsumcllem.5: |- ( ph -> 0 e. S )

  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k m
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint B f
  disjoint B m
  disjoint f ph
  disjoint m ph
  disjoint S f
  assert |- ( ph -> sum_ k e. A B e. S )

  proof
    wph
    cA
    cB
    vk
    csu
    #
    cS
    wcel
    cA
    c0
    wph
    cA
    c0
    wceq
    #
    wa
    #
    @0
    cc0
    cS
    @2
    @0
    c0
    cB
    vk
    csu
    cc0
    @2
    cA
    c0
    cB
    vk
    wph
    @1
    simpr
    sumeq1d
    cB
    vk
    sum0
    syl6eq
    wph
    cc0
    cS
    wcel
    @1
    fsumcllem.5
    adantr
    eqeltrd
    wph
    cA
    c0
    wne
    #
    wa
    vx
    vy
    cA
    cB
    cS
    vk
    wph
    cS
    cc
    wss
    @3
    fsumcllem.1
    adantr
    wph
    vx
    cv
    #
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    @4
    @5
    caddc
    co
    cS
    wcel
    @3
    fsumcllem.2
    adantlr
    wph
    cA
    cfn
    wcel
    @3
    fsumcllem.3
    adantr
    wph
    vk
    cv
    cA
    wcel
    cB
    cS
    wcel
    @3
    fsumcllem.4
    adantlr
    wph
    @3
    simpr
    fsumcl2lem
    pm2.61dane
end
