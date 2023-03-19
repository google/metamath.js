include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "grpinvcl.mm"
include "3adant2.mm"
include "3adant3.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "grpass.mm"
include "syl13anc.mm"
include "eqid.mm"
include "grprinv.mm"
include "oveq1d.mm"
include "grplid.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "wb.mm"
include "grpinvid1.mm"
include "mpbird.mm"

theorem grpinvadd
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  assume grpinvadd.b: |- B = ( Base ` G )
  assume grpinvadd.p: |- .+ = ( +g ` G )
  assume grpinvadd.n: |- N = ( invg ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( N ` ( X .+ Y ) ) = ( ( N ` Y ) .+ ( N ` X ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.pl
    co
    #
    cN
    cfv
    cY
    cN
    cfv
    #
    cX
    cN
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    @4
    @7
    c.pl
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    @3
    @9
    cX
    cY
    @7
    c.pl
    co
    #
    c.pl
    co
    #
    cX
    @6
    c.pl
    co
    #
    @10
    @3
    @0
    @1
    @2
    @7
    cB
    wcel
    #
    @9
    @13
    wceq
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    #
    @3
    @0
    @5
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    @15
    @16
    @0
    @2
    @18
    @1
    cB
    cG
    cN
    cY
    grpinvadd.b
    grpinvadd.n
    grpinvcl
    3adant2
    #
    @0
    @1
    @19
    @2
    cB
    cG
    cN
    cX
    grpinvadd.b
    grpinvadd.n
    grpinvcl
    3adant3
    #
    cB
    c.pl
    cG
    @5
    @6
    grpinvadd.b
    grpinvadd.p
    grpcl
    syl3anc
    #
    cB
    c.pl
    cG
    cX
    cY
    @7
    grpinvadd.b
    grpinvadd.p
    grpass
    syl13anc
    @3
    @12
    @6
    cX
    c.pl
    @3
    cY
    @5
    c.pl
    co
    #
    @6
    c.pl
    co
    #
    @10
    @6
    c.pl
    co
    #
    @12
    @6
    @3
    @23
    @10
    @6
    c.pl
    @0
    @2
    @23
    @10
    wceq
    @1
    cB
    c.pl
    cG
    cN
    cY
    @10
    grpinvadd.b
    grpinvadd.p
    @10
    eqid
    #
    grpinvadd.n
    grprinv
    3adant2
    oveq1d
    @3
    @0
    @2
    @18
    @19
    @24
    @12
    wceq
    @16
    @17
    @20
    @21
    cB
    c.pl
    cG
    cY
    @5
    @6
    grpinvadd.b
    grpinvadd.p
    grpass
    syl13anc
    @3
    @0
    @19
    @25
    @6
    wceq
    @16
    @21
    cB
    c.pl
    cG
    @6
    @10
    grpinvadd.b
    grpinvadd.p
    @26
    grplid
    syl2anc
    3eqtr3d
    oveq2d
    @0
    @1
    @14
    @10
    wceq
    @2
    cB
    c.pl
    cG
    cN
    cX
    @10
    grpinvadd.b
    grpinvadd.p
    @26
    grpinvadd.n
    grprinv
    3adant3
    3eqtrd
    @3
    @0
    @4
    cB
    wcel
    @15
    @8
    @11
    wb
    @16
    cB
    c.pl
    cG
    cX
    cY
    grpinvadd.b
    grpinvadd.p
    grpcl
    @22
    cB
    c.pl
    cG
    cN
    @4
    @7
    @10
    grpinvadd.b
    grpinvadd.p
    @26
    grpinvadd.n
    grpinvid1
    syl3anc
    mpbird
end
