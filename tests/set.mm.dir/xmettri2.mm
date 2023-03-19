include "wcel.mm"
include "w3a.mm"
include "cxmt.mm"
include "cfv.mm"
include "co.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "cdm.mm"
include "elfvdm.mm"
include "isxmet.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"
include "simpr.mm"
include "2ralimi.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "breq2d.mm"
include "rspc3v.mm"
include "syl5.mm"
include "3comr.mm"
include "impcom.mm"

theorem xmettri2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vw: setvar w
  let cR: class R


  assert |- ( ( D e. ( *Met ` X ) /\ ( C e. X /\ A e. X /\ B e. X ) ) -> ( A D B ) <_ ( ( C D A ) +e ( C D B ) ) )

  proof
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
    cD
    cX
    cxmt
    cfv
    wcel
    #
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
    @1
    @2
    @0
    @3
    @8
    wi
    @3
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    #
    vz
    cv
    #
    @9
    cD
    co
    #
    @12
    @10
    cD
    co
    #
    cxad
    co
    #
    cle
    wbr
    #
    vz
    cX
    wral
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @1
    @2
    @0
    w3a
    @8
    @3
    @11
    cc0
    wceq
    @9
    @10
    wceq
    wb
    #
    @17
    wa
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @18
    @3
    cX
    cX
    cxp
    cxr
    cD
    wf
    #
    @21
    @3
    @22
    @21
    wa
    #
    @3
    cX
    cxmt
    cdm
    #
    wcel
    @3
    @23
    wb
    cD
    cX
    cxmt
    elfvdm
    vx
    vy
    vz
    @24
    cD
    cX
    isxmet
    syl
    ibi
    simprd
    @20
    @17
    vx
    vy
    cX
    cX
    @19
    @17
    simpr
    2ralimi
    syl
    @16
    @8
    cA
    @10
    cD
    co
    #
    @12
    cA
    cD
    co
    #
    @14
    cxad
    co
    #
    cle
    wbr
    @4
    @26
    @12
    cB
    cD
    co
    #
    cxad
    co
    #
    cle
    wbr
    vx
    vy
    vz
    cA
    cB
    cC
    cX
    cX
    cX
    @9
    cA
    wceq
    #
    @11
    @25
    @15
    @27
    cle
    @9
    cA
    @10
    cD
    oveq1
    @30
    @13
    @26
    @14
    cxad
    @9
    cA
    @12
    cD
    oveq2
    oveq1d
    breq12d
    @10
    cB
    wceq
    #
    @25
    @4
    @27
    @29
    cle
    @10
    cB
    cA
    cD
    oveq2
    @31
    @14
    @28
    @26
    cxad
    @10
    cB
    @12
    cD
    oveq2
    oveq2d
    breq12d
    @12
    cC
    wceq
    #
    @29
    @7
    @4
    cle
    @32
    @26
    @5
    @28
    @6
    cxad
    @12
    cC
    cA
    cD
    oveq1
    @12
    cC
    cB
    cD
    oveq1
    oveq12d
    breq2d
    rspc3v
    syl5
    3comr
    impcom
end
