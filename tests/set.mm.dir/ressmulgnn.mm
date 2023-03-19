include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cplusg.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cbs.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "cvv.mm"
include "fvex.mm"
include "ssexi.mm"
include "ressplusg.mm"
include "seqeq2.mm"
include "mulgnn.mm"
include "simpr.mm"
include "sseldi.mm"
include "syldan.mm"
include "eqtr4d.mm"

theorem ressmulgnn
  let cA: class A
  let cG: class G
  let cH: class H
  let cI: class I
  let c.as: class .*
  let cN: class N
  let cX: class X
  assume ressmulgnn.1: |- H = ( G |`s A )
  assume ressmulgnn.2: |- A C_ ( Base ` G )
  assume ressmulgnn.3: |- .* = ( .g ` G )
  assume ressmulgnn.4: |- I = ( invg ` G )


  assert |- ( ( N e. NN /\ X e. A ) -> ( N ( .g ` H ) X ) = ( N .* X ) )

  proof
    cN
    cn
    wcel
    #
    cX
    cA
    wcel
    #
    wa
    #
    cN
    cX
    cH
    cmg
    cfv
    #
    co
    cN
    cG
    cplusg
    cfv
    #
    cn
    cX
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    cN
    cX
    c.as
    co
    #
    cA
    cH
    cplusg
    cfv
    #
    @6
    @3
    cH
    cN
    cX
    cA
    cG
    cbs
    cfv
    #
    wss
    cA
    cH
    cbs
    cfv
    wceq
    ressmulgnn.2
    cA
    @10
    cH
    cG
    ressmulgnn.1
    @10
    eqid
    #
    ressbas2
    ax-mp
    @9
    eqid
    @3
    eqid
    @4
    @9
    wceq
    #
    @6
    @9
    @5
    c1
    cseq
    wceq
    cA
    cvv
    wcel
    @12
    cA
    @10
    cG
    cbs
    fvex
    ressmulgnn.2
    ssexi
    cA
    @4
    cG
    cH
    cvv
    ressmulgnn.1
    @4
    eqid
    #
    ressplusg
    ax-mp
    @4
    @9
    @5
    c1
    seqeq2
    ax-mp
    mulgnn
    @0
    @1
    cX
    @10
    wcel
    @8
    @7
    wceq
    @2
    cA
    @10
    cX
    ressmulgnn.2
    @0
    @1
    simpr
    sseldi
    @10
    @4
    @6
    c.as
    cG
    cN
    cX
    @11
    @13
    ressmulgnn.3
    @6
    eqid
    mulgnn
    syldan
    eqtr4d
end
