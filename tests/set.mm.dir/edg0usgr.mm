include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "ciedg.mm"
include "wfun.mm"
include "cusgr.mm"
include "crn.mm"
include "wi.mm"
include "edgval.mm"
include "a1i.mm"
include "eqeq1d.mm"
include "wrel.mm"
include "wb.mm"
include "funrel.mm"
include "relrn0.mm"
include "bicomd.mm"
include "syl.mm"
include "wa.mm"
include "simpr.mm"
include "simpl.mm"
include "usgr0e.mm"
include "ex.mm"
include "syl6bi.mm"
include "com13.mm"
include "sylbid.mm"
include "3imp.mm"

theorem edg0usgr
  let cG: class G
  let cW: class W


  assert |- ( ( G e. W /\ ( Edg ` G ) = (/) /\ Fun ( iEdg ` G ) ) -> G e. USGraph )

  proof
    cG
    cW
    wcel
    #
    cG
    cedg
    cfv
    #
    c0
    wceq
    #
    cG
    ciedg
    cfv
    #
    wfun
    #
    cG
    cusgr
    wcel
    #
    @0
    @2
    @3
    crn
    #
    c0
    wceq
    #
    @4
    @5
    wi
    @0
    @1
    @6
    c0
    @1
    @6
    wceq
    @0
    cG
    edgval
    a1i
    eqeq1d
    @4
    @7
    @0
    @5
    @4
    @7
    @3
    c0
    wceq
    #
    @0
    @5
    wi
    @4
    @3
    wrel
    #
    @7
    @8
    wb
    @3
    funrel
    @9
    @8
    @7
    @3
    relrn0
    bicomd
    syl
    @8
    @0
    @5
    @8
    @0
    wa
    cG
    cW
    @8
    @0
    simpr
    @8
    @0
    simpl
    usgr0e
    ex
    syl6bi
    com13
    sylbid
    3imp
end
