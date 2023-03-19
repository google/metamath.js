include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cpred.mm"
include "sseqin2.mm"
include "df-pred.mm"
include "sseq1i.mm"
include "df-ss.mm"
include "in32.mm"
include "eqeq1i.mm"
include "3bitri.mm"
include "wa.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "3eqtr4g.mm"
include "eqcomd.mm"
include "syl2anb.mm"

theorem sspred
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X


  assert |- ( ( B C_ A /\ Pred ( R , A , X ) C_ B ) -> Pred ( R , A , X ) = Pred ( R , B , X ) )

  proof
    cB
    cA
    wss
    cA
    cB
    cin
    #
    cB
    wceq
    #
    @0
    cR
    ccnv
    cX
    csn
    cima
    #
    cin
    #
    cA
    @2
    cin
    #
    wceq
    #
    cA
    cR
    cX
    cpred
    #
    cB
    cR
    cX
    cpred
    #
    wceq
    @6
    cB
    wss
    #
    cB
    cA
    sseqin2
    @8
    @4
    cB
    wss
    @4
    cB
    cin
    #
    @4
    wceq
    @5
    @6
    @4
    cB
    cA
    cR
    cX
    df-pred
    #
    sseq1i
    @4
    cB
    df-ss
    @9
    @3
    @4
    cA
    @2
    cB
    in32
    eqeq1i
    3bitri
    @1
    @5
    wa
    #
    @7
    @6
    @11
    cB
    @2
    cin
    #
    @4
    @7
    @6
    @1
    @5
    @12
    @4
    wceq
    @1
    @3
    @12
    @4
    @0
    cB
    @2
    ineq1
    eqeq1d
    biimpa
    cB
    cR
    cX
    df-pred
    @10
    3eqtr4g
    eqcomd
    syl2anb
end
