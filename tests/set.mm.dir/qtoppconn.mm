include "cpconn.mm"
include "pconntop.mm"
include "cqtop.mm"
include "co.mm"
include "cuni.mm"
include "eqid.mm"
include "cnpconn.mm"
include "qtopcmplem.mm"

theorem qtoppconn
  let cF: class F
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cB: class B
  let cT: class T
  assume pconnpi1.x: |- X = U. J


  assert |- ( ( J e. PConn /\ F Fn X ) -> ( J qTop F ) e. PConn )

  proof
    cpconn
    cF
    cJ
    cX
    pconnpi1.x
    cJ
    pconntop
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
    cnpconn
    qtopcmplem
end
