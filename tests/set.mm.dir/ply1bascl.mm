include "cps1.mm"
include "cfv.mm"
include "cbs.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "eqid.mm"
include "ply1val.mm"
include "ressbasss.mm"
include "eqsstri.mm"
include "sseli.mm"

theorem ply1bascl
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  assume ply1bascl.p: |- P = ( Poly1 ` R )
  assume ply1bascl.b: |- B = ( Base ` P )


  assert |- ( F e. B -> F e. ( Base ` ( PwSer1 ` R ) ) )

  proof
    cB
    cR
    cps1
    cfv
    #
    cbs
    cfv
    #
    cF
    cB
    cP
    cbs
    cfv
    @1
    ply1bascl.b
    c1o
    cR
    cmpl
    co
    cbs
    cfv
    @1
    cP
    @0
    cP
    cR
    @0
    ply1bascl.p
    @0
    eqid
    ply1val
    @1
    eqid
    ressbasss
    eqsstri
    sseli
end
