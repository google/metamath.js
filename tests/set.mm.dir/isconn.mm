include "cv.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "cuni.mm"
include "cpr.mm"
include "wceq.mm"
include "ctop.mm"
include "cconn.mm"
include "id.mm"
include "fveq2.mm"
include "ineq12d.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "preq2d.mm"
include "eqeq12d.mm"
include "df-conn.mm"
include "elrab2.mm"

theorem isconn
  let cJ: class J
  let cX: class X
  let vj: setvar j
  assume isconn.1: |- X = U. J


  assert |- ( J e. Conn <-> ( J e. Top /\ ( J i^i ( Clsd ` J ) ) = { (/) , X } ) )

  proof
    vj
    cv
    #
    @0
    ccld
    cfv
    #
    cin
    #
    c0
    @0
    cuni
    #
    cpr
    #
    wceq
    cJ
    cJ
    ccld
    cfv
    #
    cin
    #
    c0
    cX
    cpr
    #
    wceq
    vj
    cJ
    ctop
    cconn
    @0
    cJ
    wceq
    #
    @2
    @6
    @4
    @7
    @8
    @0
    cJ
    @1
    @5
    @8
    id
    @0
    cJ
    ccld
    fveq2
    ineq12d
    @8
    @3
    cX
    c0
    @8
    @3
    cJ
    cuni
    cX
    @0
    cJ
    unieq
    isconn.1
    syl6eqr
    preq2d
    eqeq12d
    vj
    df-conn
    elrab2
end
