include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "c0g.mm"
include "grpinvcl.mm"
include "eqid.mm"
include "grprinv.mm"
include "syldan.mm"
include "grplinv.mm"
include "eqtr4d.mm"
include "wb.mm"
include "simpl.mm"
include "simpr.mm"
include "grplcan.mm"
include "syl13anc.mm"
include "mpbid.mm"

theorem grpinvinv
  let cB: class B
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume grpinvinv.b: |- B = ( Base ` G )
  assume grpinvinv.n: |- N = ( invg ` G )


  assert |- ( ( G e. Grp /\ X e. B ) -> ( N ` ( N ` X ) ) = X )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cN
    cfv
    #
    @3
    cN
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @3
    cX
    @5
    co
    #
    wceq
    #
    @4
    cX
    wceq
    #
    @2
    @6
    cG
    c0g
    cfv
    #
    @7
    @0
    @1
    @3
    cB
    wcel
    #
    @6
    @10
    wceq
    cB
    cG
    cN
    cX
    grpinvinv.b
    grpinvinv.n
    grpinvcl
    #
    cB
    @5
    cG
    cN
    @3
    @10
    grpinvinv.b
    @5
    eqid
    #
    @10
    eqid
    #
    grpinvinv.n
    grprinv
    syldan
    cB
    @5
    cG
    cN
    cX
    @10
    grpinvinv.b
    @13
    @14
    grpinvinv.n
    grplinv
    eqtr4d
    @2
    @0
    @4
    cB
    wcel
    #
    @1
    @11
    @8
    @9
    wb
    @0
    @1
    simpl
    @0
    @1
    @11
    @15
    @12
    cB
    cG
    cN
    @3
    grpinvinv.b
    grpinvinv.n
    grpinvcl
    syldan
    @0
    @1
    simpr
    @12
    cB
    @5
    cG
    @4
    cX
    @3
    grpinvinv.b
    @13
    grplcan
    syl13anc
    mpbid
end
