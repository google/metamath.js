include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "simpr.mm"
include "cr.mm"
include "ltpnf.mm"
include "syl.mm"
include "jca.mm"
include "rabid.mm"
include "sylibr.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "dfss3f.mm"
include "eqssd.mm"

theorem pimltpnf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume pimltpnf.1: |- F/ x ph
  assume pimltpnf.2: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A x
  disjoint k x
  assert |- ( ph -> { x e. A | B < +oo } = A )

  proof
    wph
    cB
    cpnf
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cA
    @1
    cA
    wss
    wph
    @0
    vx
    cA
    ssrab2
    a1i
    wph
    vx
    cv
    #
    @1
    wcel
    #
    vx
    cA
    wral
    cA
    @1
    wss
    wph
    @3
    vx
    cA
    pimltpnf.1
    wph
    @2
    cA
    wcel
    #
    @3
    wph
    @4
    wa
    #
    @4
    @0
    wa
    @3
    @5
    @4
    @0
    wph
    @4
    simpr
    @5
    cB
    cr
    wcel
    @0
    pimltpnf.2
    cB
    ltpnf
    syl
    jca
    @0
    vx
    cA
    rabid
    sylibr
    ex
    ralrimi
    vx
    cA
    @1
    vx
    cA
    nfcv
    @0
    vx
    cA
    nfrab1
    dfss3f
    sylibr
    eqssd
end
