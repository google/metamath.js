include "cv.mm"
include "ciin.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "nfcv.mm"
include "nfii1.mm"
include "nfel.mm"
include "nfan.mm"
include "adantlr.mm"
include "eliinid.mm"
include "adantll.mm"
include "sseldd.mm"
include "ex.mm"
include "ralrimi.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "dfss3.mm"

theorem iinssiin
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume iinssiin.1: |- F/ x ph
  assume iinssiin.2: |- ( ( ph /\ x e. A ) -> B C_ C )


  assert |- ( ph -> |^|_ x e. A B C_ |^|_ x e. A C )

  proof
    wph
    vy
    cv
    #
    vx
    cA
    cC
    ciin
    #
    wcel
    #
    vy
    vx
    cA
    cB
    ciin
    #
    wral
    @3
    @1
    wss
    wph
    @2
    vy
    @3
    wph
    @0
    @3
    wcel
    #
    wa
    #
    @0
    cC
    wcel
    #
    vx
    cA
    wral
    #
    @2
    @5
    @6
    vx
    cA
    wph
    @4
    vx
    iinssiin.1
    vx
    @0
    @3
    vx
    @0
    nfcv
    vx
    cA
    cB
    nfii1
    nfel
    nfan
    @5
    vx
    cv
    cA
    wcel
    #
    @6
    @5
    @8
    wa
    cB
    cC
    @0
    wph
    @8
    cB
    cC
    wss
    @4
    iinssiin.2
    adantlr
    @4
    @8
    @0
    cB
    wcel
    wph
    vx
    @0
    cA
    cB
    eliinid
    adantll
    sseldd
    ex
    ralrimi
    @0
    cvv
    wcel
    @2
    @7
    wb
    vy
    vex
    vx
    @0
    cA
    cC
    cvv
    eliin
    ax-mp
    sylibr
    ralrimiva
    vy
    @3
    @1
    dfss3
    sylibr
end
