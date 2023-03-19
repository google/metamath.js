include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "crab.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "adantr.mm"
include "cr.mm"
include "cmpt.mm"
include "a1i.mm"
include "fvmpt2d.mm"
include "breqtrrd.mm"
include "cxr.mm"
include "eqeltrd.mm"
include "rexrd.mm"
include "xrlenltd.mm"
include "mpbid.mm"
include "ex.mm"
include "ralrimi.mm"
include "rabeq0.mm"
include "sylibr.mm"

theorem pimconstlt0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  assume pimconstlt0.x: |- F/ x ph
  assume pimconstlt0.b: |- ( ph -> B e. RR )
  assume pimconstlt0.f: |- F = ( x e. A |-> B )
  assume pimconstlt0.c: |- ( ph -> C e. RR* )
  assume pimconstlt0.l: |- ( ph -> C <_ B )

  disjoint A x
  disjoint k x
  assert |- ( ph -> { x e. A | ( F ` x ) < C } = (/) )

  proof
    wph
    vx
    cv
    #
    cF
    cfv
    #
    cC
    clt
    wbr
    #
    wn
    #
    vx
    cA
    wral
    @2
    vx
    cA
    crab
    c0
    wceq
    wph
    @3
    vx
    cA
    pimconstlt0.x
    wph
    @0
    cA
    wcel
    #
    @3
    wph
    @4
    wa
    #
    cC
    @1
    cle
    wbr
    @3
    @5
    cC
    cB
    @1
    cle
    wph
    cC
    cB
    cle
    wbr
    @4
    pimconstlt0.l
    adantr
    wph
    vx
    cA
    cB
    cF
    cr
    cF
    vx
    cA
    cB
    cmpt
    wceq
    wph
    pimconstlt0.f
    a1i
    wph
    cB
    cr
    wcel
    @4
    pimconstlt0.b
    adantr
    #
    fvmpt2d
    #
    breqtrrd
    @5
    cC
    @1
    wph
    cC
    cxr
    wcel
    @4
    pimconstlt0.c
    adantr
    @5
    @1
    @5
    @1
    cB
    cr
    @7
    @6
    eqeltrd
    rexrd
    xrlenltd
    mpbid
    ex
    ralrimi
    @2
    vx
    cA
    rabeq0
    sylibr
end
