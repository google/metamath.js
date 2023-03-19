include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cgn.mm"
include "cfv.mm"
include "eqid.mm"
include "grpodivval.mm"
include "oveq1d.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "grpoinvcl.mm"
include "3adant2.mm"
include "simp3.mm"
include "grpoass.mm"
include "syl13anc.mm"
include "cgi.mm"
include "wa.mm"
include "grpolinv.mm"
include "oveq2d.mm"
include "grporid.mm"
include "3adant3.mm"
include "eqtrd.mm"

theorem grponpcan
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume grpdivf.1: |- X = ran G
  assume grpdivf.3: |- D = ( /g ` G )


  assert |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( ( A D B ) G B ) = A )

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
    cD
    co
    #
    cB
    cG
    co
    cA
    cB
    cG
    cgn
    cfv
    #
    cfv
    #
    cG
    co
    #
    cB
    cG
    co
    #
    cA
    @3
    @4
    @7
    cB
    cG
    cA
    cB
    cD
    cG
    @5
    cX
    grpdivf.1
    @5
    eqid
    #
    grpdivf.3
    grpodivval
    oveq1d
    @3
    @8
    cA
    @6
    cB
    cG
    co
    #
    cG
    co
    #
    cA
    @3
    @0
    @1
    @6
    cX
    wcel
    #
    @2
    @8
    @11
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @2
    @12
    @1
    cB
    cG
    @5
    cX
    grpdivf.1
    @9
    grpoinvcl
    3adant2
    @0
    @1
    @2
    simp3
    cA
    @6
    cB
    cG
    cX
    grpdivf.1
    grpoass
    syl13anc
    @3
    @11
    cA
    cG
    cgi
    cfv
    #
    cG
    co
    #
    cA
    @0
    @2
    @11
    @14
    wceq
    @1
    @0
    @2
    wa
    @10
    @13
    cA
    cG
    cB
    @13
    cG
    @5
    cX
    grpdivf.1
    @13
    eqid
    #
    @9
    grpolinv
    oveq2d
    3adant2
    @0
    @1
    @14
    cA
    wceq
    @2
    cA
    @13
    cG
    cX
    grpdivf.1
    @15
    grporid
    3adant3
    eqtrd
    eqtrd
    eqtrd
end
