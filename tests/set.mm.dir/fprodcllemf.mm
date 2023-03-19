include "cprod.mm"
include "cv.mm"
include "csb.mm"
include "csbeq1a.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "cbvprod.mm"
include "wcel.mm"
include "wa.mm"
include "wsbc.mm"
include "wral.mm"
include "simpr.mm"
include "ex.mm"
include "ralrimi.mm"
include "adantr.mm"
include "rspsbc.mm"
include "sylc.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbcel1g.mm"
include "ax-mp.mm"
include "sylib.mm"
include "fprodcllem.mm"
include "syl5eqel.mm"

theorem fprodcllemf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let vj: setvar j
  assume fprodcllemf.ph: |- F/ k ph
  assume fprodcllemf.s: |- ( ph -> S C_ CC )
  assume fprodcllemf.xy: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )
  assume fprodcllemf.a: |- ( ph -> A e. Fin )
  assume fprodcllemf.b: |- ( ( ph /\ k e. A ) -> B e. S )
  assume fprodcllemf.1: |- ( ph -> 1 e. S )

  disjoint A k
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint ph x
  disjoint ph y
  disjoint A j
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint B j
  disjoint S j
  disjoint j ph
  assert |- ( ph -> prod_ k e. A B e. S )

  proof
    wph
    cA
    cB
    vk
    cprod
    cA
    vk
    vj
    cv
    #
    cB
    csb
    #
    vj
    cprod
    cS
    cA
    cB
    @1
    vk
    vj
    vk
    @0
    cB
    csbeq1a
    vj
    cA
    nfcv
    vk
    cA
    nfcv
    vj
    cB
    nfcv
    vk
    @0
    cB
    nfcsb1v
    cbvprod
    wph
    vx
    vy
    cA
    @1
    cS
    vj
    fprodcllemf.s
    fprodcllemf.xy
    fprodcllemf.a
    wph
    @0
    cA
    wcel
    #
    wa
    #
    cB
    cS
    wcel
    #
    vk
    @0
    wsbc
    #
    @1
    cS
    wcel
    #
    @3
    @2
    @4
    vk
    cA
    wral
    #
    @5
    wph
    @2
    simpr
    wph
    @7
    @2
    wph
    @4
    vk
    cA
    fprodcllemf.ph
    wph
    vk
    cv
    cA
    wcel
    @4
    fprodcllemf.b
    ex
    ralrimi
    adantr
    @4
    vk
    @0
    cA
    rspsbc
    sylc
    @0
    cvv
    wcel
    @5
    @6
    wb
    vj
    vex
    vk
    @0
    cB
    cS
    cvv
    sbcel1g
    ax-mp
    sylib
    fprodcllemf.1
    fprodcllem
    syl5eqel
end
