include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "deg1fval.mm"
include "eqid.mm"
include "ply1mpl0.mm"
include "cps1.mm"
include "cfv.mm"
include "ply1bas.mm"
include "mdegnn0cl.mm"

theorem deg1nn0cl
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let c.0: class .0.
  assume deg1z.d: |- D = ( deg1 ` R )
  assume deg1z.p: |- P = ( Poly1 ` R )
  assume deg1z.z: |- .0. = ( 0g ` P )
  assume deg1nn0cl.b: |- B = ( Base ` P )


  assert |- ( ( R e. Ring /\ F e. B /\ F =/= .0. ) -> ( D ` F ) e. NN0 )

  proof
    cB
    cD
    c1o
    cR
    cmpl
    co
    #
    cR
    cF
    c1o
    c.0
    cD
    cR
    deg1z.d
    deg1fval
    @0
    eqid
    #
    cP
    cR
    @0
    c.0
    @1
    deg1z.p
    deg1z.z
    ply1mpl0
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    deg1z.p
    @2
    eqid
    deg1nn0cl.b
    ply1bas
    mdegnn0cl
end
