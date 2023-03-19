include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "wlim.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "crecs.mm"
include "csb.mm"
include "crdg.mm"
include "csbrecsg.mm"
include "csbmpt2.mm"
include "wsbc.mm"
include "csbif.mm"
include "sbcg.mm"
include "csbconstg.mm"
include "csbfv12.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "ifbieq12d.mm"
include "ifbieq2d.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "recseq.mm"
include "syl.mm"
include "df-rdg.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbrdgg
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cI: class I
  let cV: class V
  let vg: setvar g


  assert |- ( A e. V -> [_ A / x ]_ rec ( F , I ) = rec ( [_ A / x ]_ F , [_ A / x ]_ I ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vg
    cvv
    vg
    cv
    #
    c0
    wceq
    #
    cI
    @1
    cdm
    #
    wlim
    #
    @1
    crn
    cuni
    #
    @3
    cuni
    @1
    cfv
    #
    cF
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    #
    crecs
    #
    csb
    #
    vg
    cvv
    @2
    vx
    cA
    cI
    csb
    #
    @4
    @5
    @6
    vx
    cA
    cF
    csb
    #
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    #
    crecs
    #
    vx
    cA
    cF
    cI
    crdg
    #
    csb
    @14
    @13
    crdg
    @0
    @12
    vx
    cA
    @10
    csb
    #
    crecs
    #
    @19
    vx
    cA
    @10
    cV
    csbrecsg
    @0
    @21
    @18
    wceq
    @22
    @19
    wceq
    @0
    @21
    vg
    cvv
    vx
    cA
    @9
    csb
    #
    cmpt
    @18
    vx
    vg
    cA
    cV
    cvv
    @9
    csbmpt2
    @0
    vg
    cvv
    @23
    @17
    @0
    @23
    @2
    vx
    cA
    wsbc
    #
    @13
    vx
    cA
    @8
    csb
    #
    cif
    @17
    @2
    vx
    cA
    cI
    @8
    csbif
    @0
    @24
    @2
    @25
    @16
    @13
    @2
    vx
    cA
    cV
    sbcg
    @0
    @25
    @4
    vx
    cA
    wsbc
    #
    vx
    cA
    @5
    csb
    #
    vx
    cA
    @7
    csb
    #
    cif
    @16
    @4
    vx
    cA
    @5
    @7
    csbif
    @0
    @26
    @4
    @27
    @28
    @5
    @15
    @4
    vx
    cA
    cV
    sbcg
    vx
    cA
    @5
    cV
    csbconstg
    @0
    @28
    vx
    cA
    @6
    csb
    #
    @14
    cfv
    @15
    vx
    cA
    @6
    cF
    csbfv12
    @0
    @29
    @6
    @14
    vx
    cA
    @6
    cV
    csbconstg
    fveq2d
    syl5eq
    ifbieq12d
    syl5eq
    ifbieq2d
    syl5eq
    mpteq2dv
    eqtrd
    @21
    @18
    recseq
    syl
    eqtrd
    vx
    cA
    @20
    @11
    vg
    cF
    cI
    df-rdg
    csbeq2i
    vg
    @14
    @13
    df-rdg
    3eqtr4g
end
