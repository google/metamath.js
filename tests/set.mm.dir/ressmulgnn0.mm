include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "simpr.mm"
include "simplr.mm"
include "ressmulgnn.mm"
include "syl2anc.mm"
include "c0g.mm"
include "cbs.mm"
include "wss.mm"
include "eqid.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "mulg0.mm"
include "syl.mm"
include "oveq1d.mm"
include "sseldi.mm"
include "3eqtr4d.mm"
include "eqtr4d.mm"
include "wo.mm"
include "elnn0.mm"
include "biimpi.mm"
include "adantr.mm"
include "mpjaodan.mm"

theorem ressmulgnn0
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
  assume ressmulgnn0.4: |- ( 0g ` G ) = ( 0g ` H )


  assert |- ( ( N e. NN0 /\ X e. A ) -> ( N ( .g ` H ) X ) = ( N .* X ) )

  proof
    cN
    cn0
    wcel
    #
    cX
    cA
    wcel
    #
    wa
    #
    cN
    cn
    wcel
    #
    cN
    cX
    cH
    cmg
    cfv
    #
    co
    #
    cN
    cX
    c.as
    co
    #
    wceq
    #
    cN
    cc0
    wceq
    #
    @2
    @3
    wa
    @3
    @1
    @7
    @2
    @3
    simpr
    @0
    @1
    @3
    simplr
    cA
    cG
    cH
    cI
    c.as
    cN
    cX
    ressmulgnn.1
    ressmulgnn.2
    ressmulgnn.3
    ressmulgnn.4
    ressmulgnn
    syl2anc
    @2
    @8
    wa
    #
    @5
    cc0
    cX
    c.as
    co
    #
    @6
    @9
    cc0
    cX
    @4
    co
    #
    cG
    c0g
    cfv
    #
    @5
    @10
    @9
    @1
    @11
    @12
    wceq
    @0
    @1
    @8
    simplr
    #
    cA
    @4
    cH
    cX
    @12
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
    @14
    cH
    cG
    ressmulgnn.1
    @14
    eqid
    #
    ressbas2
    ax-mp
    ressmulgnn0.4
    @4
    eqid
    mulg0
    syl
    @9
    cN
    cc0
    cX
    @4
    @2
    @8
    simpr
    #
    oveq1d
    @9
    cX
    @14
    wcel
    @10
    @12
    wceq
    @9
    cA
    @14
    cX
    ressmulgnn.2
    @13
    sseldi
    @14
    c.as
    cG
    cX
    @12
    @15
    @12
    eqid
    ressmulgnn.3
    mulg0
    syl
    3eqtr4d
    @9
    cN
    cc0
    cX
    c.as
    @16
    oveq1d
    eqtr4d
    @0
    @3
    @8
    wo
    #
    @1
    @0
    @17
    cN
    elnn0
    biimpi
    adantr
    mpjaodan
end
