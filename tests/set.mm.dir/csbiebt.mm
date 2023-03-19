include "wcel.mm"
include "cvv.mm"
include "wnfc.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "csb.mm"
include "wb.mm"
include "elex.mm"
include "wa.mm"
include "wsbc.mm"
include "spsbc.mm"
include "adantr.mm"
include "simpl.mm"
include "biimt.mm"
include "csbeq1a.mm"
include "eqeq1d.mm"
include "bitr3d.mm"
include "adantl.mm"
include "nfv.mm"
include "nfnfc1.mm"
include "nfan.mm"
include "nfcsb1v.mm"
include "a1i.mm"
include "simpr.mm"
include "nfeqd.mm"
include "sbciedf.mm"
include "sylibd.mm"
include "id.mm"
include "nfan1.mm"
include "biimprcd.mm"
include "alrimi.mm"
include "ex.mm"
include "impbid.mm"
include "sylan.mm"

theorem csbiebt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V

  disjoint A x
  assert |- ( ( A e. V /\ F/_ x C ) -> ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    vx
    cC
    wnfc
    #
    vx
    cv
    cA
    wceq
    #
    cB
    cC
    wceq
    #
    wi
    #
    vx
    wal
    #
    vx
    cA
    cB
    csb
    #
    cC
    wceq
    #
    wb
    cA
    cV
    elex
    @0
    @1
    wa
    #
    @5
    @7
    @8
    @5
    @4
    vx
    cA
    wsbc
    #
    @7
    @0
    @5
    @9
    wi
    @1
    @4
    vx
    cA
    cvv
    spsbc
    adantr
    @8
    @4
    @7
    vx
    cA
    cvv
    @0
    @1
    simpl
    @2
    @4
    @7
    wb
    @8
    @2
    @3
    @4
    @7
    @2
    @3
    biimt
    @2
    cB
    @6
    cC
    vx
    cA
    cB
    csbeq1a
    eqeq1d
    #
    bitr3d
    adantl
    @0
    @1
    vx
    @0
    vx
    nfv
    vx
    cC
    nfnfc1
    #
    nfan
    @8
    vx
    @6
    cC
    vx
    @6
    wnfc
    #
    @8
    vx
    cA
    cB
    nfcsb1v
    #
    a1i
    @0
    @1
    simpr
    nfeqd
    sbciedf
    sylibd
    @1
    @7
    @5
    wi
    @0
    @1
    @7
    @5
    @1
    @7
    wa
    @4
    vx
    @1
    @7
    vx
    @11
    @1
    vx
    @6
    cC
    @12
    @1
    @13
    a1i
    @1
    id
    nfeqd
    nfan1
    @7
    @4
    @1
    @2
    @3
    @7
    @10
    biimprcd
    adantl
    alrimi
    ex
    adantl
    impbid
    sylan
end
