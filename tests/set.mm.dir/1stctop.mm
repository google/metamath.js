include "c1stc.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "eqid.mm"
include "is1stc.mm"
include "simplbi.mm"

theorem 1stctop
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( J e. 1stc -> J e. Top )

  proof
    cJ
    c1stc
    wcel
    cJ
    ctop
    wcel
    vy
    cv
    #
    com
    cdom
    wbr
    vx
    cv
    #
    vz
    cv
    #
    wcel
    @1
    @0
    @2
    cpw
    cin
    cuni
    wcel
    wi
    vz
    cJ
    wral
    wa
    vy
    cJ
    cpw
    wrex
    vx
    cJ
    cuni
    #
    wral
    vx
    vy
    vz
    cJ
    @3
    @3
    eqid
    is1stc
    simplbi
end
