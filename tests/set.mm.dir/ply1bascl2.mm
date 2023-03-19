include "wcel.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cps1.mm"
include "eqid.mm"
include "ply1bas.mm"
include "eleq2i.mm"
include "biimpi.mm"

theorem ply1bascl2
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  assume ply1bascl.p: |- P = ( Poly1 ` R )
  assume ply1bascl.b: |- B = ( Base ` P )


  assert |- ( F e. B -> F e. ( Base ` ( 1o mPoly R ) ) )

  proof
    cF
    cB
    wcel
    cF
    c1o
    cR
    cmpl
    co
    cbs
    cfv
    #
    wcel
    cB
    @0
    cF
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    ply1bascl.p
    @1
    eqid
    ply1bascl.b
    ply1bas
    eleq2i
    biimpi
end
