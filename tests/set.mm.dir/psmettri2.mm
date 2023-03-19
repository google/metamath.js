include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "elfvex.mm"
include "ispsmet.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "ralrimiva.mm"
include "wi.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "breq2d.mm"
include "rspc3v.mm"
include "3comr.mm"
include "mpan9.mm"

theorem psmettri2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( D e. ( PsMet ` X ) /\ ( C e. X /\ A e. X /\ B e. X ) ) -> ( A D B ) <_ ( ( C D A ) +e ( C D B ) ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cD
    co
    #
    vc
    cv
    #
    @1
    cD
    co
    #
    @4
    @2
    cD
    co
    #
    cxad
    co
    #
    cle
    wbr
    #
    vc
    cX
    wral
    vb
    cX
    wral
    #
    va
    cX
    wral
    #
    cC
    cX
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    cA
    cB
    cD
    co
    #
    cC
    cA
    cD
    co
    #
    cC
    cB
    cD
    co
    #
    cxad
    co
    #
    cle
    wbr
    #
    @0
    @9
    va
    cX
    @0
    @1
    cX
    wcel
    wa
    @1
    @1
    cD
    co
    cc0
    wceq
    #
    @9
    @0
    @19
    @9
    wa
    #
    va
    cX
    @0
    cX
    cX
    cxp
    cxr
    cD
    wf
    #
    @20
    va
    cX
    wral
    #
    @0
    @21
    @22
    wa
    #
    @0
    cX
    cvv
    wcel
    @0
    @23
    wb
    cD
    cX
    cpsmet
    elfvex
    va
    vb
    vc
    cD
    cvv
    cX
    ispsmet
    syl
    ibi
    simprd
    r19.21bi
    simprd
    ralrimiva
    @12
    @13
    @11
    @10
    @18
    wi
    @8
    @18
    cA
    @2
    cD
    co
    #
    @4
    cA
    cD
    co
    #
    @6
    cxad
    co
    #
    cle
    wbr
    @14
    @25
    @4
    cB
    cD
    co
    #
    cxad
    co
    #
    cle
    wbr
    va
    vb
    vc
    cA
    cB
    cC
    cX
    cX
    cX
    @1
    cA
    wceq
    #
    @3
    @24
    @7
    @26
    cle
    @1
    cA
    @2
    cD
    oveq1
    @29
    @5
    @25
    @6
    cxad
    @1
    cA
    @4
    cD
    oveq2
    oveq1d
    breq12d
    @2
    cB
    wceq
    #
    @24
    @14
    @26
    @28
    cle
    @2
    cB
    cA
    cD
    oveq2
    @30
    @6
    @27
    @25
    cxad
    @2
    cB
    @4
    cD
    oveq2
    oveq2d
    breq12d
    @4
    cC
    wceq
    #
    @28
    @17
    @14
    cle
    @31
    @25
    @15
    @27
    @16
    cxad
    @4
    cC
    cA
    cD
    oveq1
    @4
    cC
    cB
    cD
    oveq1
    oveq12d
    breq2d
    rspc3v
    3comr
    mpan9
end
