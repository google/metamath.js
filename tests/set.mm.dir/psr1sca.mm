include "wcel.mm"
include "c1o.mm"
include "cmps.mm"
include "co.mm"
include "c0.mm"
include "con0.mm"
include "eqid.mm"
include "psr1val.mm"
include "cxp.mm"
include "wss.mm"
include "0ss.mm"
include "a1i.mm"
include "1on.mm"
include "id.mm"
include "opsrsca.mm"

theorem psr1sca
  let cP: class P
  let cR: class R
  let cV: class V
  assume psr1lmod.p: |- P = ( PwSer1 ` R )


  assert |- ( R e. V -> R = ( Scalar ` P ) )

  proof
    cR
    cV
    wcel
    #
    cR
    c1o
    cR
    cmps
    co
    #
    c0
    c1o
    cP
    con0
    cV
    @1
    eqid
    cR
    cP
    psr1lmod.p
    psr1val
    c0
    c1o
    c1o
    cxp
    #
    wss
    @0
    @2
    0ss
    a1i
    c1o
    con0
    wcel
    @0
    1on
    a1i
    @0
    id
    opsrsca
end
