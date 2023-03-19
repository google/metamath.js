include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "cxmt.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "wa.mm"
include "elfvex.mm"
include "adantr.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cxr.mm"
include "cxad.mm"
include "simpllr.mm"
include "simpr.mm"
include "simplrl.mm"
include "fovrnd.mm"
include "simplrr.mm"
include "rexadd.mm"
include "syl2anc.mm"
include "breq2d.mm"
include "ralbidva.mm"
include "anbi2d.mm"
include "2ralbidva.mm"
include "wss.mm"
include "ressxr.mm"
include "fss.mm"
include "sylancl.mm"
include "biantrurd.mm"
include "bitr3d.mm"
include "pm5.32da.mm"
include "ancom.mm"
include "syl6bb.mm"
include "ismet.mm"
include "isxmet.mm"
include "anbi1d.mm"
include "3bitr4d.mm"
include "pm5.21nii.mm"

theorem ismet2
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  let cC: class C


  assert |- ( D e. ( Met ` X ) <-> ( D e. ( *Met ` X ) /\ D : ( X X. X ) --> RR ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cX
    cvv
    wcel
    #
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cX
    cX
    cxp
    #
    cr
    cD
    wf
    #
    wa
    #
    cD
    cX
    cme
    elfvex
    @2
    @1
    @4
    cD
    cX
    cxmt
    elfvex
    adantr
    @1
    @4
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    #
    cc0
    wceq
    @6
    @7
    wceq
    wb
    #
    @8
    vz
    cv
    #
    @6
    cD
    co
    #
    @10
    @7
    cD
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    vz
    cX
    wral
    #
    wa
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    #
    @3
    cxr
    cD
    wf
    #
    @9
    @8
    @11
    @12
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
    wa
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    #
    @4
    wa
    #
    @0
    @5
    @1
    @18
    @4
    @25
    wa
    @26
    @1
    @4
    @17
    @25
    @1
    @4
    wa
    #
    @24
    @17
    @25
    @27
    @23
    @16
    vx
    vy
    cX
    cX
    @27
    @6
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    wa
    #
    wa
    #
    @22
    @15
    @9
    @31
    @21
    @14
    vz
    cX
    @31
    @10
    cX
    wcel
    #
    wa
    #
    @20
    @13
    @8
    cle
    @33
    @11
    cr
    wcel
    @12
    cr
    wcel
    @20
    @13
    wceq
    @33
    @10
    @6
    cr
    cX
    cX
    cD
    @1
    @4
    @30
    @32
    simpllr
    #
    @31
    @32
    simpr
    #
    @27
    @28
    @29
    @32
    simplrl
    fovrnd
    @33
    @10
    @7
    cr
    cX
    cX
    cD
    @34
    @35
    @27
    @28
    @29
    @32
    simplrr
    fovrnd
    @11
    @12
    rexadd
    syl2anc
    breq2d
    ralbidva
    anbi2d
    2ralbidva
    @27
    @19
    @24
    @27
    @4
    cr
    cxr
    wss
    @19
    @1
    @4
    simpr
    ressxr
    @3
    cr
    cxr
    cD
    fss
    sylancl
    biantrurd
    bitr3d
    pm5.32da
    @4
    @25
    ancom
    syl6bb
    vx
    vy
    vz
    cvv
    cD
    cX
    ismet
    @1
    @2
    @25
    @4
    vx
    vy
    vz
    cvv
    cD
    cX
    isxmet
    anbi1d
    3bitr4d
    pm5.21nii
end
