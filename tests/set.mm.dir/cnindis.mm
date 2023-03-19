include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cpr.mm"
include "ccn.mm"
include "co.mm"
include "cmap.mm"
include "cv.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "wceq.mm"
include "wo.mm"
include "elpri.mm"
include "ctop.mm"
include "topontop.mm"
include "ad2antrr.mm"
include "0opn.mm"
include "syl.mm"
include "imaeq2.mm"
include "ima0.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "fimacnv.mm"
include "adantl.mm"
include "toponmax.mm"
include "eqeltrd.mm"
include "jaod.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "ex.mm"
include "pm4.71d.mm"
include "wb.mm"
include "id.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "indistopon.mm"
include "iscn.mm"
include "sylan2.mm"
include "3bitr4rd.mm"
include "eqrdv.mm"

theorem cnindis
  let cA: class A
  let cJ: class J
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cY: class Y


  assert |- ( ( J e. ( TopOn ` X ) /\ A e. V ) -> ( J Cn { (/) , A } ) = ( A ^m X ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    vf
    cJ
    c0
    cA
    cpr
    #
    ccn
    co
    #
    cA
    cX
    cmap
    co
    #
    @2
    cX
    cA
    vf
    cv
    #
    wf
    #
    @7
    @6
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
    @3
    wral
    #
    wa
    #
    @6
    @5
    wcel
    #
    @6
    @4
    wcel
    #
    @2
    @7
    @12
    @2
    @7
    @12
    @2
    @7
    wa
    #
    @11
    vx
    @3
    @9
    @3
    wcel
    @9
    c0
    wceq
    #
    @9
    cA
    wceq
    #
    wo
    @16
    @11
    @9
    c0
    cA
    elpri
    @16
    @17
    @11
    @18
    @16
    @11
    @17
    c0
    cJ
    wcel
    #
    @16
    cJ
    ctop
    wcel
    #
    @19
    @0
    @20
    @1
    @7
    cX
    cJ
    topontop
    ad2antrr
    cJ
    0opn
    syl
    @17
    @10
    c0
    cJ
    @17
    @10
    @8
    c0
    cima
    c0
    @9
    c0
    @8
    imaeq2
    @8
    ima0
    syl6eq
    eleq1d
    syl5ibrcom
    @16
    @11
    @18
    @8
    cA
    cima
    #
    cJ
    wcel
    @16
    @21
    cX
    cJ
    @7
    @21
    cX
    wceq
    @2
    cX
    cA
    @6
    fimacnv
    adantl
    @0
    cX
    cJ
    wcel
    #
    @1
    @7
    cX
    cJ
    toponmax
    #
    ad2antrr
    eqeltrd
    @18
    @10
    @21
    cJ
    @9
    cA
    @8
    imaeq2
    eleq1d
    syl5ibrcom
    jaod
    syl5
    ralrimiv
    ex
    pm4.71d
    @1
    @1
    @22
    @14
    @7
    wb
    @0
    @1
    id
    @23
    cA
    cX
    @6
    cV
    cJ
    elmapg
    syl2anr
    @1
    @0
    @3
    cA
    ctopon
    cfv
    wcel
    @15
    @13
    wb
    cA
    cV
    indistopon
    vx
    @6
    cJ
    @3
    cX
    cA
    iscn
    sylan2
    3bitr4rd
    eqrdv
end
