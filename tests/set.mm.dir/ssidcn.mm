include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "ccn.mm"
include "co.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wss.mm"
include "wf.mm"
include "iscn.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ax-mp.mm"
include "biantrur.mm"
include "syl6bbr.mm"
include "cnvresid.mm"
include "imaeq1i.mm"
include "wceq.mm"
include "cuni.mm"
include "elssuni.mm"
include "adantl.mm"
include "toponuni.mm"
include "ad2antlr.mm"
include "sseqtr4d.mm"
include "resiima.mm"
include "syl.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "dfss3.mm"
include "bitrd.mm"

theorem ssidcn
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cP: class P


  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` X ) ) -> ( ( _I |` X ) e. ( J Cn K ) <-> K C_ J ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cK
    @0
    wcel
    #
    wa
    #
    cid
    cX
    cres
    #
    cJ
    cK
    ccn
    co
    wcel
    #
    @4
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vx
    cK
    wral
    #
    cK
    cJ
    wss
    #
    @3
    @5
    cX
    cX
    @4
    wf
    #
    @10
    wa
    @10
    vx
    @4
    cJ
    cK
    cX
    cX
    iscn
    @12
    @10
    cX
    cX
    @4
    wf1o
    @12
    cX
    f1oi
    cX
    cX
    @4
    f1of
    ax-mp
    biantrur
    syl6bbr
    @3
    @10
    @7
    cJ
    wcel
    #
    vx
    cK
    wral
    @11
    @3
    @9
    @13
    vx
    cK
    @3
    @7
    cK
    wcel
    #
    wa
    #
    @8
    @7
    cJ
    @15
    @8
    @4
    @7
    cima
    #
    @7
    @6
    @4
    @7
    cX
    cnvresid
    imaeq1i
    @15
    @7
    cX
    wss
    @16
    @7
    wceq
    @15
    @7
    cK
    cuni
    #
    cX
    @14
    @7
    @17
    wss
    @3
    @7
    cK
    elssuni
    adantl
    @2
    cX
    @17
    wceq
    @1
    @14
    cX
    cK
    toponuni
    ad2antlr
    sseqtr4d
    cX
    @7
    resiima
    syl
    syl5eq
    eleq1d
    ralbidva
    vx
    cK
    cJ
    dfss3
    syl6bbr
    bitrd
end
