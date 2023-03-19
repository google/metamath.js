include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "simpr.mm"
include "cr.mm"
include "cmpt.mm"
include "wceq.mm"
include "adantr.mm"
include "fvmpt2d.mm"
include "eqbrtrd.mm"
include "jca.mm"
include "rabid.mm"
include "sylibr.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "dfss3f.mm"
include "eqssd.mm"

theorem pimconstlt1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  assume pimconstlt1.1: |- F/ x ph
  assume pimconstlt1.2: |- ( ph -> B e. RR )
  assume pimconstlt1.3: |- F = ( x e. A |-> B )
  assume pimconstlt1.4: |- ( ph -> B < C )

  disjoint A x
  disjoint k x
  assert |- ( ph -> { x e. A | ( F ` x ) < C } = A )

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
    vx
    cA
    crab
    #
    cA
    @3
    cA
    wss
    wph
    @2
    vx
    cA
    ssrab2
    a1i
    wph
    @0
    @3
    wcel
    #
    vx
    cA
    wral
    cA
    @3
    wss
    wph
    @4
    vx
    cA
    pimconstlt1.1
    wph
    @0
    cA
    wcel
    #
    @4
    wph
    @5
    wa
    #
    @5
    @2
    wa
    @4
    @6
    @5
    @2
    wph
    @5
    simpr
    @6
    @1
    cB
    cC
    clt
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
    pimconstlt1.3
    a1i
    wph
    cB
    cr
    wcel
    @5
    pimconstlt1.2
    adantr
    fvmpt2d
    wph
    cB
    cC
    clt
    wbr
    @5
    pimconstlt1.4
    adantr
    eqbrtrd
    jca
    @2
    vx
    cA
    rabid
    sylibr
    ex
    ralrimi
    vx
    cA
    @3
    vx
    cA
    nfcv
    @2
    vx
    cA
    nfrab1
    dfss3f
    sylibr
    eqssd
end
