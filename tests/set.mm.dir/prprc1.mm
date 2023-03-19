include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "c0.mm"
include "wceq.mm"
include "cpr.mm"
include "snprc.mm"
include "cun.mm"
include "uneq1.mm"
include "df-pr.mm"
include "uncom.mm"
include "un0.mm"
include "eqtr2i.mm"
include "3eqtr4g.mm"
include "sylbi.mm"

theorem prprc1
  let cA: class A
  let cB: class B


  assert |- ( -. A e. _V -> { A , B } = { B } )

  proof
    cA
    cvv
    wcel
    wn
    cA
    csn
    #
    c0
    wceq
    #
    cA
    cB
    cpr
    #
    cB
    csn
    #
    wceq
    cA
    snprc
    @1
    @0
    @3
    cun
    c0
    @3
    cun
    #
    @2
    @3
    @0
    c0
    @3
    uneq1
    cA
    cB
    df-pr
    @4
    @3
    c0
    cun
    @3
    c0
    @3
    uncom
    @3
    un0
    eqtr2i
    3eqtr4g
    sylbi
end
