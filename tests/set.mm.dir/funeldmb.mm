include "wfun.mm"
include "c0.mm"
include "crn.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cdm.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "fvelrn.mm"
include "ex.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "sylibd.mm"
include "con3d.mm"
include "impancom.mm"
include "ndmfv.mm"
include "impbid1.mm"
include "necon2abid.mm"

theorem funeldmb
  let cA: class A
  let cF: class F


  assert |- ( ( Fun F /\ -. (/) e. ran F ) -> ( A e. dom F <-> ( F ` A ) =/= (/) ) )

  proof
    cF
    wfun
    #
    c0
    cF
    crn
    #
    wcel
    #
    wn
    #
    wa
    #
    cA
    cF
    cdm
    wcel
    #
    cA
    cF
    cfv
    #
    c0
    @4
    @6
    c0
    wceq
    #
    @5
    wn
    #
    @0
    @7
    @3
    @8
    @0
    @7
    wa
    #
    @5
    @2
    @9
    @5
    @6
    @1
    wcel
    #
    @2
    @0
    @5
    @10
    wi
    @7
    @0
    @5
    @10
    cA
    cF
    fvelrn
    ex
    adantr
    @7
    @10
    @2
    wb
    @0
    @6
    c0
    @1
    eleq1
    adantl
    sylibd
    con3d
    impancom
    cA
    cF
    ndmfv
    impbid1
    necon2abid
end
