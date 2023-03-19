include "cwun.mm"
include "wcel.mm"
include "wtr.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "cfn.mm"
include "cdif.mm"
include "wb.mm"
include "iswun.mm"
include "ibi.mm"
include "3simpa.mm"
include "ralimi.mm"
include "3ad2ant3.mm"
include "pwinfig.mm"
include "3syl.mm"

theorem pwinfi2
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y


  assert |- ( U e. WUni -> ( A e. ( U \ Fin ) <-> ~P A e. ( U \ Fin ) ) )

  proof
    cU
    cwun
    wcel
    #
    cU
    wtr
    #
    cU
    c0
    wne
    #
    vx
    cv
    #
    cuni
    cU
    wcel
    #
    @3
    cpw
    cU
    wcel
    #
    @3
    vy
    cv
    cpr
    cU
    wcel
    vy
    cU
    wral
    #
    w3a
    #
    vx
    cU
    wral
    #
    w3a
    #
    @4
    @5
    wa
    #
    vx
    cU
    wral
    #
    cA
    cU
    cfn
    cdif
    #
    wcel
    cA
    cpw
    @12
    wcel
    wb
    @0
    @9
    vx
    vy
    cU
    cwun
    iswun
    ibi
    @8
    @1
    @11
    @2
    @7
    @10
    vx
    cU
    @4
    @5
    @6
    3simpa
    ralimi
    3ad2ant3
    vx
    cA
    cU
    pwinfig
    3syl
end
