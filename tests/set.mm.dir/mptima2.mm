include "cmpt.mm"
include "cima.mm"
include "cin.mm"
include "crn.mm"
include "wceq.mm"
include "mptima.mm"
include "a1i.mm"
include "wss.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "syl.mm"
include "mpteq1d.mm"
include "rneqd.mm"
include "eqtrd.mm"

theorem mptima2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume mptima2.1: |- ( ph -> C C_ A )

  disjoint A x
  disjoint C x
  assert |- ( ph -> ( ( x e. A |-> B ) " C ) = ran ( x e. C |-> B ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    cC
    cima
    #
    vx
    cA
    cC
    cin
    #
    cB
    cmpt
    #
    crn
    #
    vx
    cC
    cB
    cmpt
    #
    crn
    @0
    @3
    wceq
    wph
    vx
    cA
    cB
    cC
    mptima
    a1i
    wph
    @2
    @4
    wph
    vx
    @1
    cC
    cB
    wph
    cC
    cA
    wss
    #
    @1
    cC
    wceq
    #
    mptima2.1
    @5
    @6
    cC
    cA
    sseqin2
    biimpi
    syl
    mpteq1d
    rneqd
    eqtrd
end
