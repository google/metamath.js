include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "wtru.mm"
include "c0.mm"
include "c1o.mm"
include "psr1val.mm"
include "cxp.mm"
include "wss.mm"
include "0ss.mm"
include "a1i.mm"
include "opsrbas.mm"
include "trud.mm"
include "eqtr4i.mm"

theorem psr1bas2
  let cB: class B
  let cR: class R
  let cS: class S
  let cO: class O
  let vr: setvar r
  assume psr1val.1: |- S = ( PwSer1 ` R )
  assume psr1bas2.b: |- B = ( Base ` S )
  assume psr1bas2.o: |- O = ( 1o mPwSer R )


  assert |- B = ( Base ` O )

  proof
    cB
    cS
    cbs
    cfv
    #
    cO
    cbs
    cfv
    #
    psr1bas2.b
    @1
    @0
    wceq
    wtru
    cR
    cO
    c0
    c1o
    cS
    psr1bas2.o
    cR
    cS
    psr1val.1
    psr1val
    c0
    c1o
    c1o
    cxp
    #
    wss
    wtru
    @2
    0ss
    a1i
    opsrbas
    trud
    eqtr4i
end
