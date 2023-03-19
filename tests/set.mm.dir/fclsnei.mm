include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wa.mm"
include "cfcls.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "csn.mm"
include "cnei.mm"
include "cuni.mm"
include "eqid.mm"
include "fclselbas.mm"
include "wceq.mm"
include "toponuni.mm"
include "adantr.mm"
include "eleq2d.mm"
include "syl5ibr.mm"
include "wi.mm"
include "fclsneii.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "a1i.mm"
include "jcad.mm"
include "ctop.mm"
include "topontop.mm"
include "ad3antrrr.mm"
include "simprl.mm"
include "simprr.mm"
include "opnneip.mm"
include "syl3anc.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "expr.mm"
include "com23.mm"
include "ralrimdva.mm"
include "imdistanda.mm"
include "fclsopn.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem fclsnei
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vo: setvar o
  let vx: setvar x
  let cS: class S
  let cU: class U

  disjoint n s
  disjoint A n
  disjoint A s
  disjoint F n
  disjoint F s
  disjoint J n
  disjoint J s
  disjoint X s
  disjoint n o
  disjoint o s
  disjoint A o
  disjoint n x
  disjoint o x
  disjoint F o
  disjoint s x
  disjoint F x
  disjoint J o
  disjoint J x
  disjoint S s
  disjoint S x
  disjoint X o
  disjoint X x
  disjoint U x
  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) ) -> ( A e. ( J fClus F ) <-> ( A e. X /\ A. n e. ( ( nei ` J ) ` { A } ) A. s e. F ( n i^i s ) =/= (/) ) ) )

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
    wcel
    #
    wa
    #
    cA
    cJ
    cF
    cfcls
    co
    wcel
    #
    cA
    cX
    wcel
    #
    vn
    cv
    #
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
    vn
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    #
    wral
    #
    wa
    #
    @2
    @3
    @4
    @11
    @3
    @4
    @2
    cA
    cJ
    cuni
    #
    wcel
    cA
    cF
    cJ
    @13
    @13
    eqid
    fclselbas
    @2
    cX
    @13
    cA
    @0
    cX
    @13
    wceq
    @1
    cX
    cJ
    toponuni
    adantr
    eleq2d
    syl5ibr
    @3
    @11
    wi
    @2
    @3
    @8
    vn
    vs
    @10
    cF
    @3
    @5
    @10
    wcel
    @6
    cF
    wcel
    @8
    cA
    @6
    cF
    cJ
    @5
    fclsneii
    3expb
    ralrimivva
    a1i
    jcad
    @2
    @12
    @4
    cA
    vo
    cv
    #
    wcel
    #
    @14
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
    wa
    @3
    @2
    @4
    @11
    @20
    @2
    @4
    wa
    #
    @11
    @19
    vo
    cJ
    @21
    @14
    cJ
    wcel
    #
    wa
    @15
    @11
    @18
    @21
    @22
    @15
    @11
    @18
    wi
    #
    @21
    @22
    @15
    wa
    #
    wa
    #
    @14
    @10
    wcel
    #
    @23
    @25
    cJ
    ctop
    wcel
    #
    @22
    @15
    @26
    @0
    @27
    @1
    @4
    @24
    cX
    cJ
    topontop
    ad3antrrr
    @21
    @22
    @15
    simprl
    @21
    @22
    @15
    simprr
    cA
    cJ
    @14
    opnneip
    syl3anc
    @9
    @18
    vn
    @14
    @10
    @5
    @14
    wceq
    #
    @8
    @17
    vs
    cF
    @28
    @7
    @16
    c0
    @5
    @14
    @6
    ineq1
    neeq1d
    ralbidv
    rspcv
    syl
    expr
    com23
    ralrimdva
    imdistanda
    cA
    vo
    cF
    cJ
    cX
    vs
    fclsopn
    sylibrd
    impbid
end
