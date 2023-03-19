include "clo.mm"
include "wcel.mm"
include "cnop.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "ch0o.mm"
include "wb.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cnmoo.mm"
include "co.mm"
include "eqid.mm"
include "hhnmoi.mm"
include "c0o.mm"
include "hh0oi.mm"
include "clno.mm"
include "hhlnoi.mm"
include "hhnv.mm"
include "nmlno0i.mm"
include "ax-mp.mm"

theorem nmlnop0iHIL
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nmlnop0.1: |- T e. LinOp


  assert |- ( ( normop ` T ) = 0 <-> T = 0hop )

  proof
    cT
    clo
    wcel
    cT
    cnop
    cfv
    cc0
    wceq
    cT
    ch0o
    wceq
    wb
    nmlnop0.1
    cT
    cva
    csm
    cop
    cno
    cop
    #
    clo
    cnop
    @0
    ch0o
    @0
    @0
    @0
    cnmoo
    co
    #
    @0
    eqid
    #
    @1
    eqid
    hhnmoi
    @0
    @0
    @0
    c0o
    co
    #
    @2
    @3
    eqid
    hh0oi
    @0
    @0
    @0
    clno
    co
    #
    @2
    @4
    eqid
    hhlnoi
    @0
    @2
    hhnv
    #
    @5
    nmlno0i
    ax-mp
end
