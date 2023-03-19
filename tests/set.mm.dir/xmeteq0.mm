include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "cdm.mm"
include "elfvdm.mm"
include "isxmet.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"
include "simpl.mm"
include "2ralimi.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "oveq2.mm"
include "eqeq2.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem xmeteq0
  let cA: class A
  let cB: class B
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  let cC: class C


  assert |- ( ( D e. ( *Met ` X ) /\ A e. X /\ B e. X ) -> ( ( A D B ) = 0 <-> A = B ) )

  proof
    cD
    cX
    cxmt
    cfv
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
    cA
    cB
    cD
    co
    #
    cc0
    wceq
    #
    cA
    cB
    wceq
    #
    wb
    #
    @0
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
    #
    @7
    @8
    wceq
    #
    wb
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
    wa
    @6
    @0
    @12
    @9
    vz
    cv
    #
    @7
    cD
    co
    @14
    @8
    cD
    co
    cxad
    co
    cle
    wbr
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
    @13
    @0
    cX
    cX
    cxp
    cxr
    cD
    wf
    #
    @17
    @0
    @18
    @17
    wa
    #
    @0
    cX
    cxmt
    cdm
    #
    wcel
    @0
    @19
    wb
    cD
    cX
    cxmt
    elfvdm
    vx
    vy
    vz
    @20
    cD
    cX
    isxmet
    syl
    ibi
    simprd
    @16
    @12
    vx
    vy
    cX
    cX
    @12
    @15
    simpl
    2ralimi
    syl
    @12
    @6
    cA
    @8
    cD
    co
    #
    cc0
    wceq
    #
    cA
    @8
    wceq
    #
    wb
    vx
    vy
    cA
    cB
    cX
    cX
    @7
    cA
    wceq
    #
    @10
    @22
    @11
    @23
    @24
    @9
    @21
    cc0
    @7
    cA
    @8
    cD
    oveq1
    eqeq1d
    @7
    cA
    @8
    eqeq1
    bibi12d
    @8
    cB
    wceq
    #
    @22
    @4
    @23
    @5
    @25
    @21
    @3
    cc0
    @8
    cB
    cA
    cD
    oveq2
    eqeq1d
    @8
    cB
    cA
    eqeq2
    bibi12d
    rspc2v
    syl5com
    3impib
end
