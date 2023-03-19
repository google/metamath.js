include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "cin.mm"
include "csn.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "iccleub.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "simprr.mm"
include "iccgelb.mm"
include "wb.mm"
include "eliccxr.mm"
include "syl.mm"
include "jca.mm"
include "xrletri3.mm"
include "mpbir2and.mm"
include "ex.mm"
include "adantr.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simplrl.mm"
include "simpr.mm"
include "ubicc2.mm"
include "eqeltrd.mm"
include "syl31anc.mm"
include "simpll3.mm"
include "simplrr.mm"
include "lbicc2.mm"
include "impbid.mm"
include "elin.mm"
include "velsn.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem iccintsng
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A <_ B /\ B <_ C ) ) -> ( ( A [,] B ) i^i ( B [,] C ) ) = { B } )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cC
    cle
    wbr
    #
    wa
    #
    wa
    #
    vx
    cA
    cB
    cicc
    co
    #
    cB
    cC
    cicc
    co
    #
    cin
    #
    cB
    csn
    #
    @7
    vx
    cv
    #
    @8
    wcel
    #
    @12
    @9
    wcel
    #
    wa
    #
    @12
    cB
    wceq
    #
    @12
    @10
    wcel
    @12
    @11
    wcel
    @7
    @15
    @16
    @3
    @15
    @16
    wi
    @6
    @3
    @15
    @16
    @3
    @15
    wa
    #
    @16
    @12
    cB
    cle
    wbr
    #
    cB
    @12
    cle
    wbr
    #
    @17
    @0
    @1
    @13
    @18
    @0
    @1
    @2
    @15
    simpl1
    @0
    @1
    @2
    @15
    simpl2
    #
    @3
    @13
    @14
    simprl
    #
    cA
    cB
    @12
    iccleub
    syl3anc
    @17
    @1
    @2
    @14
    @19
    @20
    @0
    @1
    @2
    @15
    simpl3
    @3
    @13
    @14
    simprr
    cB
    cC
    @12
    iccgelb
    syl3anc
    @17
    @12
    cxr
    wcel
    #
    @1
    wa
    @16
    @18
    @19
    wa
    wb
    @17
    @22
    @1
    @17
    @13
    @22
    @21
    @12
    cA
    cB
    eliccxr
    syl
    @20
    jca
    @12
    cB
    xrletri3
    syl
    mpbir2and
    ex
    adantr
    @7
    @16
    @15
    @7
    @16
    wa
    #
    @13
    @14
    @23
    @0
    @1
    @4
    @16
    @13
    @0
    @1
    @2
    @6
    @16
    simpll1
    @0
    @1
    @2
    @6
    @16
    simpll2
    #
    @3
    @4
    @5
    @16
    simplrl
    @7
    @16
    simpr
    #
    @0
    @1
    @4
    w3a
    #
    @16
    wa
    @12
    cB
    @8
    @26
    @16
    simpr
    @26
    cB
    @8
    wcel
    @16
    cA
    cB
    ubicc2
    adantr
    eqeltrd
    syl31anc
    @23
    @1
    @2
    @5
    @16
    @14
    @24
    @0
    @1
    @2
    @6
    @16
    simpll3
    @3
    @4
    @5
    @16
    simplrr
    @25
    @1
    @2
    @5
    w3a
    #
    @16
    wa
    @12
    cB
    @9
    @27
    @16
    simpr
    @27
    cB
    @9
    wcel
    @16
    cB
    cC
    lbicc2
    adantr
    eqeltrd
    syl31anc
    jca
    ex
    impbid
    @12
    @8
    @9
    elin
    vx
    cB
    velsn
    3bitr4g
    eqrdv
end
