include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "cpr.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "cun.mm"
include "prcom.mm"
include "df-pr.mm"
include "eqtri.mm"
include "fveq1i.mm"
include "fvunsn.mm"
include "syl5eq.mm"
include "3ad2ant3.mm"
include "fvsng.mm"
include "3adant3.mm"
include "eqtrd.mm"

theorem fvpr2g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W


  assert |- ( ( B e. V /\ D e. W /\ A =/= B ) -> ( { <. A , C >. , <. B , D >. } ` B ) = D )

  proof
    cB
    cV
    wcel
    #
    cD
    cW
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    cB
    cA
    cC
    cop
    #
    cB
    cD
    cop
    #
    cpr
    #
    cfv
    #
    cB
    @4
    csn
    #
    cfv
    #
    cD
    @2
    @0
    @6
    @8
    wceq
    @1
    @2
    @6
    cB
    @7
    @3
    csn
    cun
    #
    cfv
    @8
    cB
    @5
    @9
    @5
    @4
    @3
    cpr
    @9
    @3
    @4
    prcom
    @4
    @3
    df-pr
    eqtri
    fveq1i
    @7
    cA
    cC
    cB
    fvunsn
    syl5eq
    3ad2ant3
    @0
    @1
    @8
    cD
    wceq
    @2
    cB
    cD
    cV
    cW
    fvsng
    3adant3
    eqtrd
end
