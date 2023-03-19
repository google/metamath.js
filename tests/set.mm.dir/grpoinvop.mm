include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cgi.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "grpoinvcl.mm"
include "3adant2.mm"
include "3adant3.mm"
include "grpocl.mm"
include "syl3anc.mm"
include "grpoass.mm"
include "syl13anc.mm"
include "eqid.mm"
include "grporinv.mm"
include "oveq1d.mm"
include "grpolid.mm"
include "syldan.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "wb.mm"
include "grpoinvid1.mm"
include "mpbird.mm"

theorem grpoinvop
  let cA: class A
  let cB: class B
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume grpasscan1.1: |- X = ran G
  assume grpasscan1.2: |- N = ( inv ` G )


  assert |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( N ` ( A G B ) ) = ( ( N ` B ) G ( N ` A ) ) )

  proof
    cG
    cgr
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cG
    co
    #
    cN
    cfv
    cB
    cN
    cfv
    #
    cA
    cN
    cfv
    #
    cG
    co
    #
    wceq
    #
    @4
    @7
    cG
    co
    #
    cG
    cgi
    cfv
    #
    wceq
    #
    @3
    @9
    cA
    cB
    @7
    cG
    co
    #
    cG
    co
    #
    cA
    @6
    cG
    co
    #
    @10
    @3
    @0
    @1
    @2
    @7
    cX
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
    cX
    wcel
    #
    @6
    cX
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
    cX
    grpasscan1.1
    grpasscan1.2
    grpoinvcl
    3adant2
    #
    @0
    @1
    @19
    @2
    cA
    cG
    cN
    cX
    grpasscan1.1
    grpasscan1.2
    grpoinvcl
    #
    3adant3
    #
    @5
    @6
    cG
    cX
    grpasscan1.1
    grpocl
    syl3anc
    #
    cA
    cB
    @7
    cG
    cX
    grpasscan1.1
    grpoass
    syl13anc
    @3
    @12
    @6
    cA
    cG
    @3
    cB
    @5
    cG
    co
    #
    @6
    cG
    co
    #
    @10
    @6
    cG
    co
    #
    @12
    @6
    @3
    @24
    @10
    @6
    cG
    @0
    @2
    @24
    @10
    wceq
    @1
    cB
    @10
    cG
    cN
    cX
    grpasscan1.1
    @10
    eqid
    #
    grpasscan1.2
    grporinv
    3adant2
    oveq1d
    @3
    @0
    @2
    @18
    @19
    @25
    @12
    wceq
    @16
    @17
    @20
    @22
    cB
    @5
    @6
    cG
    cX
    grpasscan1.1
    grpoass
    syl13anc
    @0
    @1
    @26
    @6
    wceq
    #
    @2
    @0
    @1
    @19
    @28
    @21
    @6
    @10
    cG
    cX
    grpasscan1.1
    @27
    grpolid
    syldan
    3adant3
    3eqtr3d
    oveq2d
    @0
    @1
    @14
    @10
    wceq
    @2
    cA
    @10
    cG
    cN
    cX
    grpasscan1.1
    @27
    grpasscan1.2
    grporinv
    3adant3
    3eqtrd
    @3
    @0
    @4
    cX
    wcel
    @15
    @8
    @11
    wb
    @16
    cA
    cB
    cG
    cX
    grpasscan1.1
    grpocl
    @23
    @4
    @7
    @10
    cG
    cN
    cX
    grpasscan1.1
    @27
    grpasscan1.2
    grpoinvid1
    syl3anc
    mpbird
end
