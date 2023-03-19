include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "cin.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "cfne.mm"
include "df-fne.mm"
include "relopabi.mm"

theorem fnerel
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Rel Fne

  proof
    vx
    cv
    #
    cuni
    vy
    cv
    #
    cuni
    wceq
    vz
    cv
    #
    @1
    @2
    cpw
    cin
    cuni
    wss
    vz
    @0
    wral
    wa
    vx
    vy
    cfne
    vx
    vy
    vz
    df-fne
    relopabi
end
