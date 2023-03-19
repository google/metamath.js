include "cfcls.mm"
include "co.mm"
include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "cuni.mm"
include "wa.mm"
include "ctopon.mm"
include "cfv.mm"
include "cfil.mm"
include "wb.mm"
include "eqid.mm"
include "fclsfil.mm"
include "fclstopon.mm"
include "mpbird.mm"
include "fclsopn.mm"
include "syl2anc.mm"
include "ibi.mm"
include "simprd.mm"
include "wceq.mm"
include "eleq2.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl.mm"
include "ineq2.mm"
include "syl8.mm"
include "3imp2.mm"

theorem fclsopni
  let cA: class A
  let cS: class S
  let cU: class U
  let cF: class F
  let cJ: class J
  let vo: setvar o
  let vs: setvar s
  let cX: class X


  assert |- ( ( A e. ( J fClus F ) /\ ( U e. J /\ A e. U /\ S e. F ) ) -> ( U i^i S ) =/= (/) )

  proof
    cA
    cJ
    cF
    cfcls
    co
    wcel
    #
    cU
    cJ
    wcel
    #
    cA
    cU
    wcel
    #
    cS
    cF
    wcel
    #
    cU
    cS
    cin
    #
    c0
    wne
    #
    @0
    @1
    @2
    cU
    vs
    cv
    #
    cin
    #
    c0
    wne
    #
    vs
    cF
    wral
    #
    @3
    @5
    wi
    @0
    cA
    vo
    cv
    #
    wcel
    #
    @10
    @6
    cin
    #
    c0
    wne
    #
    vs
    cF
    wral
    #
    wi
    #
    vo
    cJ
    wral
    #
    @1
    @2
    @9
    wi
    #
    wi
    @0
    cA
    cJ
    cuni
    #
    wcel
    #
    @16
    @0
    @19
    @16
    wa
    #
    @0
    cJ
    @18
    ctopon
    cfv
    wcel
    #
    cF
    @18
    cfil
    cfv
    wcel
    #
    @0
    @20
    wb
    @0
    @21
    @22
    cA
    cF
    cJ
    @18
    @18
    eqid
    fclsfil
    #
    cA
    cF
    cJ
    @18
    fclstopon
    mpbird
    @23
    cA
    vo
    cF
    cJ
    @18
    vs
    fclsopn
    syl2anc
    ibi
    simprd
    @15
    @17
    vo
    cU
    cJ
    @10
    cU
    wceq
    #
    @11
    @2
    @14
    @9
    @10
    cU
    cA
    eleq2
    @24
    @13
    @8
    vs
    cF
    @24
    @12
    @7
    c0
    @10
    cU
    @6
    ineq1
    neeq1d
    ralbidv
    imbi12d
    rspccv
    syl
    @8
    @5
    vs
    cS
    cF
    @6
    cS
    wceq
    @7
    @4
    c0
    @6
    cS
    cU
    ineq2
    neeq1d
    rspccv
    syl8
    3imp2
end
