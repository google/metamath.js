include "cvv.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "ctp.mm"
include "cpr.mm"
include "wceq.mm"
include "ianor.mm"
include "csn.mm"
include "cun.mm"
include "prprc2.mm"
include "uneq1d.mm"
include "tprot.mm"
include "df-tp.mm"
include "eqtri.mm"
include "prcom.mm"
include "df-pr.mm"
include "3eqtr4g.mm"
include "nne.mm"
include "tppreq3.mm"
include "eqcoms.mm"
include "sylbi.mm"
include "jaoi.mm"

theorem tpprceq3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( -. ( C e. _V /\ C =/= B ) -> { A , B , C } = { A , B } )

  proof
    cC
    cvv
    wcel
    #
    cC
    cB
    wne
    #
    wa
    wn
    @0
    wn
    #
    @1
    wn
    #
    wo
    cA
    cB
    cC
    ctp
    #
    cA
    cB
    cpr
    #
    wceq
    #
    @0
    @1
    ianor
    @2
    @6
    @3
    @2
    cB
    cC
    cpr
    #
    cA
    csn
    #
    cun
    #
    cB
    csn
    #
    @8
    cun
    #
    @4
    @5
    @2
    @7
    @10
    @8
    cB
    cC
    prprc2
    uneq1d
    @4
    cB
    cC
    cA
    ctp
    @9
    cA
    cB
    cC
    tprot
    cB
    cC
    cA
    df-tp
    eqtri
    @5
    cB
    cA
    cpr
    @11
    cA
    cB
    prcom
    cB
    cA
    df-pr
    eqtri
    3eqtr4g
    @3
    cC
    cB
    wceq
    @6
    cC
    cB
    nne
    @6
    cB
    cC
    cA
    cB
    cC
    tppreq3
    eqcoms
    sylbi
    jaoi
    sylbi
end
