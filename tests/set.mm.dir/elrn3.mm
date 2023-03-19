include "crn.mm"
include "wcel.mm"
include "ccnv.mm"
include "cdm.mm"
include "csn.mm"
include "cres.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "df-rn.mm"
include "eleq2i.mm"
include "eldm3.mm"
include "wceq.mm"
include "cnvxp.mm"
include "ineq2i.mm"
include "cnvin.mm"
include "df-res.mm"
include "3eqtr4ri.mm"
include "eqeq1i.mm"
include "wrel.mm"
include "wb.mm"
include "wss.mm"
include "inss2.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "cnveq0.mm"
include "ax-mp.mm"
include "bitr4i.mm"
include "necon3bii.mm"
include "3bitri.mm"

theorem elrn3
  let cA: class A
  let cB: class B


  assert |- ( A e. ran B <-> ( B i^i ( _V X. { A } ) ) =/= (/) )

  proof
    cA
    cB
    crn
    #
    wcel
    cA
    cB
    ccnv
    #
    cdm
    #
    wcel
    @1
    cA
    csn
    #
    cres
    #
    c0
    wne
    cB
    cvv
    @3
    cxp
    #
    cin
    #
    c0
    wne
    @0
    @2
    cA
    cB
    df-rn
    eleq2i
    cA
    @1
    eldm3
    @4
    c0
    @6
    c0
    @4
    c0
    wceq
    @6
    ccnv
    #
    c0
    wceq
    #
    @6
    c0
    wceq
    #
    @4
    @7
    c0
    @1
    @5
    ccnv
    #
    cin
    @1
    @3
    cvv
    cxp
    #
    cin
    @7
    @4
    @10
    @11
    @1
    cvv
    @3
    cnvxp
    ineq2i
    cB
    @5
    cnvin
    @1
    @3
    df-res
    3eqtr4ri
    eqeq1i
    @6
    wrel
    #
    @9
    @8
    wb
    @6
    @5
    wss
    @5
    wrel
    @12
    cB
    @5
    inss2
    cvv
    @3
    relxp
    @6
    @5
    relss
    mp2
    @6
    cnveq0
    ax-mp
    bitr4i
    necon3bii
    3bitri
end
