include "clo.mm"
include "wcel.mm"
include "cnop.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "ch0o.mm"
include "wb.mm"
include "cif.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "0lnop.mm"
include "elimel.mm"
include "nmlnop0iHIL.mm"
include "dedth.mm"

theorem nmlnop0
  let cT: class T


  assert |- ( T e. LinOp -> ( ( normop ` T ) = 0 <-> T = 0hop ) )

  proof
    cT
    clo
    wcel
    #
    cT
    cnop
    cfv
    #
    cc0
    wceq
    #
    cT
    ch0o
    wceq
    #
    wb
    @0
    cT
    ch0o
    cif
    #
    cnop
    cfv
    #
    cc0
    wceq
    #
    @4
    ch0o
    wceq
    #
    wb
    cT
    ch0o
    cT
    @4
    wceq
    #
    @2
    @6
    @3
    @7
    @8
    @1
    @5
    cc0
    cT
    @4
    cnop
    fveq2
    eqeq1d
    cT
    @4
    ch0o
    eqeq1
    bibi12d
    @4
    cT
    ch0o
    clo
    0lnop
    elimel
    nmlnop0iHIL
    dedth
end
