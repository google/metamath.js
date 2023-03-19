include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "cuni.mm"
include "cv.mm"
include "cint.mm"
include "cin.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "cmoore.mm"
include "bj-ismoorec.mm"
include "sylib.mm"
include "wi.mm"
include "elpw2g.mm"
include "biimparc.mm"
include "wceq.mm"
include "inteq.mm"
include "ineq2d.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "syl.mm"
include "expimpd.mm"
include "sylc.mm"

theorem bj-ismoored
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume bj-ismoored.1: |- ( ph -> A e. Moore_ )
  assume bj-ismoored.2: |- ( ph -> B C_ A )


  assert |- ( ph -> ( U. A i^i |^| B ) e. A )

  proof
    wph
    cB
    cA
    wss
    #
    cA
    cvv
    wcel
    #
    cA
    cuni
    #
    vx
    cv
    #
    cint
    #
    cin
    #
    cA
    wcel
    #
    vx
    cA
    cpw
    #
    wral
    #
    wa
    #
    @2
    cB
    cint
    #
    cin
    #
    cA
    wcel
    #
    bj-ismoored.2
    wph
    cA
    cmoore
    wcel
    @9
    bj-ismoored.1
    vx
    cA
    bj-ismoorec
    sylib
    @0
    @1
    @8
    @12
    @0
    @1
    wa
    cB
    @7
    wcel
    #
    @8
    @12
    wi
    @1
    @13
    @0
    cB
    cA
    cvv
    elpw2g
    biimparc
    @6
    @12
    vx
    cB
    @7
    @3
    cB
    wceq
    #
    @5
    @11
    cA
    @14
    @4
    @10
    @2
    @3
    cB
    inteq
    ineq2d
    eleq1d
    rspcv
    syl
    expimpd
    sylc
end
