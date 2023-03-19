include "cprod.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "prodeq1.mm"
include "prod0.mm"
include "syl6eq.mm"
include "adantl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "cc.mm"
include "wss.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "adantlr.mm"
include "cfn.mm"
include "simpr.mm"
include "fprodcl2lem.mm"
include "pm2.61dane.mm"

theorem fprodcllem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  assume fprodcllem.1: |- ( ph -> S C_ CC )
  assume fprodcllem.2: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )
  assume fprodcllem.3: |- ( ph -> A e. Fin )
  assume fprodcllem.4: |- ( ( ph /\ k e. A ) -> B e. S )
  assume fprodcllem.5: |- ( ph -> 1 e. S )

  disjoint A k
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint ph x
  disjoint ph y
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint x y
  assert |- ( ph -> prod_ k e. A B e. S )

  proof
    wph
    cA
    cB
    vk
    cprod
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
    @0
    c1
    cS
    @1
    @0
    c1
    wceq
    wph
    @1
    @0
    c0
    cB
    vk
    cprod
    c1
    cA
    c0
    cB
    vk
    prodeq1
    cB
    vk
    prod0
    syl6eq
    adantl
    wph
    c1
    cS
    wcel
    @1
    fprodcllem.5
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
    @2
    fprodcllem.1
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
    @3
    @4
    cmul
    co
    cS
    wcel
    @2
    fprodcllem.2
    adantlr
    wph
    cA
    cfn
    wcel
    @2
    fprodcllem.3
    adantr
    wph
    vk
    cv
    cA
    wcel
    cB
    cS
    wcel
    @2
    fprodcllem.4
    adantlr
    wph
    @2
    simpr
    fprodcl2lem
    pm2.61dane
end
