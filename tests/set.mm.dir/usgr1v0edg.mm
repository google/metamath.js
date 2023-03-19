include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "ciedg.mm"
include "wfun.mm"
include "w3a.mm"
include "cusgr.mm"
include "c0.mm"
include "crn.mm"
include "cedg.mm"
include "wb.mm"
include "usgr1v.mm"
include "3adant3.mm"
include "wrel.mm"
include "funrel.mm"
include "relrn0.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "edgval.mm"
include "eqcomi.mm"
include "eqeq1i.mm"
include "a1i.mm"
include "3bitrd.mm"

theorem usgr1v0edg
  let cA: class A
  let cG: class G
  let cW: class W
  let vx: setvar x
  let cX: class X


  assert |- ( ( G e. W /\ ( Vtx ` G ) = { A } /\ Fun ( iEdg ` G ) ) -> ( G e. USGraph <-> ( Edg ` G ) = (/) ) )

  proof
    cG
    cW
    wcel
    #
    cG
    cvtx
    cfv
    cA
    csn
    wceq
    #
    cG
    ciedg
    cfv
    #
    wfun
    #
    w3a
    #
    cG
    cusgr
    wcel
    #
    @2
    c0
    wceq
    #
    @2
    crn
    #
    c0
    wceq
    #
    cG
    cedg
    cfv
    #
    c0
    wceq
    #
    @0
    @1
    @5
    @6
    wb
    @3
    cA
    cG
    cW
    usgr1v
    3adant3
    @3
    @0
    @6
    @8
    wb
    #
    @1
    @3
    @2
    wrel
    @11
    @2
    funrel
    @2
    relrn0
    syl
    3ad2ant3
    @8
    @10
    wb
    @4
    @7
    @9
    c0
    @9
    @7
    cG
    edgval
    eqcomi
    eqeq1i
    a1i
    3bitrd
end
