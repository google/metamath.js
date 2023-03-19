include "cops.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cplt.mm"
include "cfv.mm"
include "cple.mm"
include "eqid.mm"
include "ople1.mm"
include "wn.mm"
include "cpo.mm"
include "opposet.mm"
include "ad2antrr.mm"
include "op1cl.mm"
include "simplr.mm"
include "simpr.mm"
include "pltnle.mm"
include "syl31anc.mm"
include "ex.mm"
include "mt2d.mm"
include "simpll.mm"
include "cvrlt.mm"
include "mtand.mm"

theorem ncvr1
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let cK: class K
  let cX: class X
  assume ncvr1.b: |- B = ( Base ` K )
  assume ncvr1.u: |- .1. = ( 1. ` K )
  assume ncvr1.c: |- C = ( <o ` K )


  assert |- ( ( K e. OP /\ X e. B ) -> -. .1. C X )

  proof
    cK
    cops
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    c.1
    cX
    cC
    wbr
    #
    c.1
    cX
    cK
    cplt
    cfv
    #
    wbr
    #
    @2
    @5
    cX
    c.1
    cK
    cple
    cfv
    #
    wbr
    #
    cB
    c.1
    cK
    @6
    cX
    ncvr1.b
    @6
    eqid
    #
    ncvr1.u
    ople1
    @2
    @5
    @7
    wn
    #
    @2
    @5
    wa
    cK
    cpo
    wcel
    #
    c.1
    cB
    wcel
    #
    @1
    @5
    @9
    @0
    @10
    @1
    @5
    cK
    opposet
    ad2antrr
    @0
    @11
    @1
    @5
    cB
    c.1
    cK
    ncvr1.b
    ncvr1.u
    op1cl
    #
    ad2antrr
    @0
    @1
    @5
    simplr
    @2
    @5
    simpr
    cB
    @4
    cK
    @6
    c.1
    cX
    ncvr1.b
    @8
    @4
    eqid
    #
    pltnle
    syl31anc
    ex
    mt2d
    @2
    @3
    wa
    @0
    @11
    @1
    @3
    @5
    @0
    @1
    @3
    simpll
    @0
    @11
    @1
    @3
    @12
    ad2antrr
    @0
    @1
    @3
    simplr
    @2
    @3
    simpr
    cops
    cB
    cC
    @4
    cK
    c.1
    cX
    ncvr1.b
    @13
    ncvr1.c
    cvrlt
    syl31anc
    mtand
end
