include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "deg1fval.mm"
include "eqid.mm"
include "cps1.mm"
include "cfv.mm"
include "ply1bas.mm"
include "mdegxrf.mm"

theorem deg1xrf
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  assume deg1xrf.d: |- D = ( deg1 ` R )
  assume deg1xrf.p: |- P = ( Poly1 ` R )
  assume deg1xrf.b: |- B = ( Base ` P )


  assert |- D : B --> RR*

  proof
    cB
    cD
    c1o
    cR
    cmpl
    co
    #
    cR
    c1o
    cD
    cR
    deg1xrf.d
    deg1fval
    @0
    eqid
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    deg1xrf.p
    @1
    eqid
    deg1xrf.b
    ply1bas
    mdegxrf
end
