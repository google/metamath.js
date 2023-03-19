include "cconn.mm"
include "conntop.mm"
include "cqtop.mm"
include "co.mm"
include "cuni.mm"
include "eqid.mm"
include "cnconn.mm"
include "qtopcmplem.mm"

theorem qtopconn
  let cF: class F
  let cJ: class J
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cY: class Y
  assume qtopcmp.1: |- X = U. J


  assert |- ( ( J e. Conn /\ F Fn X ) -> ( J qTop F ) e. Conn )

  proof
    cconn
    cF
    cJ
    cX
    qtopcmp.1
    cJ
    conntop
    cF
    cJ
    cJ
    cF
    cqtop
    co
    #
    cX
    @0
    cuni
    #
    @1
    eqid
    cnconn
    qtopcmplem
end
