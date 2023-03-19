include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wa.mm"
include "ctop.mm"
include "cuni.mm"
include "cfcls.mm"
include "co.mm"
include "cv.mm"
include "ccl.mm"
include "wral.mm"
include "wb.mm"
include "topontop.mm"
include "adantr.mm"
include "toponuni.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "w3a.mm"
include "eqid.mm"
include "isfcls.mm"
include "df-3an.mm"
include "bitri.mm"
include "baib.mm"
include "syl2anc.mm"

theorem isfcls2
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vo: setvar o
  let cU: class U
  let cS: class S

  disjoint A s
  disjoint F s
  disjoint J s
  disjoint X s
  disjoint o s
  disjoint A o
  disjoint F o
  disjoint J o
  disjoint U o
  disjoint U s
  disjoint S s
  disjoint X o
  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) ) -> ( A e. ( J fClus F ) <-> A. s e. F A e. ( ( cls ` J ) ` s ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    wa
    cJ
    ctop
    wcel
    #
    cF
    cJ
    cuni
    #
    cfil
    cfv
    #
    wcel
    #
    cA
    cJ
    cF
    cfcls
    co
    wcel
    #
    cA
    vs
    cv
    cJ
    ccl
    cfv
    cfv
    wcel
    vs
    cF
    wral
    #
    wb
    @0
    @3
    @2
    cX
    cJ
    topontop
    adantr
    @0
    @2
    @6
    @0
    @1
    @5
    cF
    @0
    cX
    @4
    cfil
    cX
    cJ
    toponuni
    fveq2d
    eleq2d
    biimpa
    @7
    @3
    @6
    wa
    #
    @8
    @7
    @3
    @6
    @8
    w3a
    @9
    @8
    wa
    cA
    cF
    cJ
    @4
    vs
    @4
    eqid
    isfcls
    @3
    @6
    @8
    df-3an
    bitri
    baib
    syl2anc
end
