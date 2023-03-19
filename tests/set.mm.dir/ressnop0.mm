include "wcel.mm"
include "wn.mm"
include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "csn.mm"
include "cres.mm"
include "c0.mm"
include "wceq.mm"
include "opelxp1.mm"
include "con3i.mm"
include "cin.mm"
include "df-res.mm"
include "incom.mm"
include "eqtri.mm"
include "disjsn.mm"
include "biimpri.mm"
include "syl5eq.mm"
include "syl.mm"

theorem ressnop0
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( -. A e. C -> ( { <. A , B >. } |` C ) = (/) )

  proof
    cA
    cC
    wcel
    #
    wn
    cA
    cB
    cop
    #
    cC
    cvv
    cxp
    #
    wcel
    #
    wn
    #
    @1
    csn
    #
    cC
    cres
    #
    c0
    wceq
    @3
    @0
    cA
    cB
    cC
    cvv
    opelxp1
    con3i
    @4
    @6
    @2
    @5
    cin
    #
    c0
    @6
    @5
    @2
    cin
    @7
    @5
    cC
    df-res
    @5
    @2
    incom
    eqtri
    @7
    c0
    wceq
    @4
    @2
    @1
    disjsn
    biimpri
    syl5eq
    syl
end
