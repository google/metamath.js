include "ch0o.mm"
include "wne.mm"
include "cnop.mm"
include "cfv.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "nmlnop0iHIL.mm"
include "necon3bii.mm"
include "chil.mm"
include "wf.mm"
include "wb.mm"
include "lnopfi.mm"
include "nmopgt0.mm"
include "ax-mp.mm"
include "bitr3i.mm"

theorem nmlnopgt0i
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nmlnop0.1: |- T e. LinOp


  assert |- ( T =/= 0hop <-> 0 < ( normop ` T ) )

  proof
    cT
    ch0o
    wne
    cT
    cnop
    cfv
    #
    cc0
    wne
    #
    cc0
    @0
    clt
    wbr
    #
    @0
    cc0
    cT
    ch0o
    cT
    nmlnop0.1
    nmlnop0iHIL
    necon3bii
    chil
    chil
    cT
    wf
    @1
    @2
    wb
    cT
    nmlnop0.1
    lnopfi
    cT
    nmopgt0
    ax-mp
    bitr3i
end
