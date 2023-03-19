include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "wb.mm"
include "elspansn.mm"
include "adantr.mm"
include "sneq.mm"
include "fveq2d.mm"
include "ad2antll.mm"
include "wi.mm"
include "cc0.mm"
include "oveq1.mm"
include "ax-hvmul0.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "eqeq1.mm"
include "biimprd.mm"
include "sylan9.mm"
include "necon3d.mm"
include "com23.mm"
include "impd.mm"
include "spansncol.mm"
include "3expia.mm"
include "syld.mm"
include "exp4b.mm"
include "imp43.mm"
include "eqtrd.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"

theorem spansneleq
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( B e. ~H /\ A =/= 0h ) -> ( A e. ( span ` { B } ) -> ( span ` { A } ) = ( span ` { B } ) ) )

  proof
    cB
    chil
    wcel
    #
    cA
    c0v
    wne
    #
    wa
    #
    cA
    cB
    csn
    cspn
    cfv
    #
    wcel
    #
    cA
    vx
    cv
    #
    cB
    csm
    co
    #
    wceq
    #
    vx
    cc
    wrex
    #
    cA
    csn
    #
    cspn
    cfv
    #
    @3
    wceq
    #
    @0
    @4
    @8
    wb
    @1
    vx
    cB
    cA
    elspansn
    adantr
    @2
    @7
    @11
    vx
    cc
    @2
    @5
    cc
    wcel
    #
    @7
    wa
    wa
    @10
    @6
    csn
    #
    cspn
    cfv
    #
    @3
    @7
    @10
    @14
    wceq
    @2
    @12
    @7
    @9
    @13
    cspn
    cA
    @6
    sneq
    fveq2d
    ad2antll
    @0
    @1
    @12
    @7
    @14
    @3
    wceq
    #
    @0
    @12
    @1
    @7
    @15
    wi
    @0
    @12
    @1
    @7
    @15
    @0
    @12
    wa
    @1
    @7
    wa
    #
    @5
    cc0
    wne
    #
    @15
    @0
    @16
    @17
    wi
    @12
    @0
    @1
    @7
    @17
    @0
    @7
    @1
    @17
    @0
    @7
    @1
    @17
    wi
    @0
    @7
    wa
    @5
    cc0
    cA
    c0v
    @0
    @5
    cc0
    wceq
    #
    @6
    c0v
    wceq
    #
    @7
    cA
    c0v
    wceq
    #
    @0
    @18
    @19
    @18
    @0
    @6
    cc0
    cB
    csm
    co
    c0v
    @5
    cc0
    cB
    csm
    oveq1
    cB
    ax-hvmul0
    sylan9eqr
    ex
    @7
    @20
    @19
    cA
    @6
    c0v
    eqeq1
    biimprd
    sylan9
    necon3d
    ex
    com23
    impd
    adantr
    @0
    @12
    @17
    @15
    cB
    @5
    spansncol
    3expia
    syld
    exp4b
    com23
    imp43
    eqtrd
    rexlimdvaa
    sylbid
end
