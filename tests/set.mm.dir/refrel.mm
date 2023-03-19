include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cref.mm"
include "df-ref.mm"
include "relopabi.mm"

theorem refrel
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Rel Ref

  proof
    vy
    cv
    #
    cuni
    vx
    cv
    #
    cuni
    wceq
    vz
    cv
    vw
    cv
    wss
    vw
    @0
    wrex
    vz
    @1
    wral
    wa
    vx
    vy
    cref
    vx
    vy
    vz
    vw
    df-ref
    relopabi
end
