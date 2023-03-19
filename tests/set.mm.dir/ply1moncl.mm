include "crg.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cmnd.mm"
include "co.mm"
include "ply1ring.mm"
include "ringmgp.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"

theorem ply1moncl
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.ex: class .^
  let cN: class N
  let cX: class X
  assume ply1moncl.p: |- P = ( Poly1 ` R )
  assume ply1moncl.x: |- X = ( var1 ` R )
  assume ply1moncl.n: |- N = ( mulGrp ` P )
  assume ply1moncl.e: |- .^ = ( .g ` N )
  assume ply1moncl.b: |- B = ( Base ` P )


  assert |- ( ( R e. Ring /\ D e. NN0 ) -> ( D .^ X ) e. B )

  proof
    cR
    crg
    wcel
    #
    cD
    cn0
    wcel
    #
    wa
    cN
    cmnd
    wcel
    #
    @1
    cX
    cB
    wcel
    #
    cD
    cX
    c.ex
    co
    cB
    wcel
    @0
    @2
    @1
    @0
    cP
    crg
    wcel
    @2
    cP
    cR
    ply1moncl.p
    ply1ring
    cP
    cN
    ply1moncl.n
    ringmgp
    syl
    adantr
    @0
    @1
    simpr
    @0
    @3
    @1
    cB
    cP
    cR
    cX
    ply1moncl.x
    ply1moncl.p
    ply1moncl.b
    vr1cl
    adantr
    cB
    c.ex
    cN
    cD
    cX
    cB
    cP
    cN
    ply1moncl.n
    ply1moncl.b
    mgpbas
    ply1moncl.e
    mulgnn0cl
    syl3anc
end
