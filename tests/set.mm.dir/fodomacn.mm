include "wacn.mm"
include "wcel.mm"
include "wfo.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "wex.mm"
include "foelrn.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "acni3.mm"
include "sylan2.mm"
include "cvv.mm"
include "wf1.mm"
include "simpll.mm"
include "acnrcl.mm"
include "syl.mm"
include "weq.mm"
include "wi.mm"
include "simprl.mm"
include "wb.mm"
include "simprr.mm"
include "id.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "eqeqan12d.mm"
include "anandis.mm"
include "sylan.mm"
include "syl5ibr.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "f1dom2g.mm"
include "syl3anc.mm"
include "exlimddv.mm"
include "ex.mm"

theorem fodomacn
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. AC_ B -> ( F : A -onto-> B -> B ~<_ A ) )

  proof
    cA
    cB
    wacn
    #
    wcel
    #
    cA
    cB
    cF
    wfo
    #
    cB
    cA
    cdom
    wbr
    #
    @1
    @2
    wa
    #
    cB
    cA
    vf
    cv
    #
    wf
    #
    vx
    cv
    #
    @7
    @5
    cfv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    cB
    wral
    #
    wa
    #
    @3
    vf
    @2
    @1
    @7
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vy
    cA
    wrex
    #
    vx
    cB
    wral
    @12
    vf
    wex
    @2
    @16
    vx
    cB
    vy
    cA
    cB
    @7
    cF
    foelrn
    ralrimiva
    @15
    @10
    vx
    vy
    cB
    vf
    cA
    @13
    @8
    wceq
    @14
    @9
    @7
    @13
    @8
    cF
    fveq2
    eqeq2d
    acni3
    sylan2
    @4
    @12
    wa
    #
    cB
    cvv
    wcel
    #
    @1
    cB
    cA
    @5
    wf1
    #
    @3
    @17
    @1
    @18
    @1
    @2
    @12
    simpll
    #
    cB
    cA
    acnrcl
    syl
    @20
    @17
    @6
    @13
    @5
    cfv
    #
    vz
    cv
    #
    @5
    cfv
    #
    wceq
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    cB
    wral
    vy
    cB
    wral
    @19
    @4
    @6
    @11
    simprl
    @17
    @26
    vy
    vz
    cB
    cB
    @24
    @25
    @17
    @13
    cB
    wcel
    #
    @22
    cB
    wcel
    #
    wa
    #
    wa
    @21
    cF
    cfv
    #
    @23
    cF
    cfv
    #
    wceq
    #
    @21
    @23
    cF
    fveq2
    @17
    @11
    @29
    @25
    @32
    wb
    #
    @4
    @6
    @11
    simprr
    @11
    @27
    @28
    @33
    @11
    @27
    wa
    @11
    @28
    wa
    @13
    @30
    @22
    @31
    @10
    @13
    @30
    wceq
    vx
    @13
    cB
    vx
    vy
    weq
    #
    @7
    @13
    @9
    @30
    @34
    id
    @34
    @8
    @21
    cF
    @7
    @13
    @5
    fveq2
    fveq2d
    eqeq12d
    rspccva
    @10
    @22
    @31
    wceq
    vx
    @22
    cB
    vx
    vz
    weq
    #
    @7
    @22
    @9
    @31
    @35
    id
    @35
    @8
    @23
    cF
    @7
    @22
    @5
    fveq2
    fveq2d
    eqeq12d
    rspccva
    eqeqan12d
    anandis
    sylan
    syl5ibr
    ralrimivva
    vy
    vz
    cB
    cA
    @5
    dff13
    sylanbrc
    cB
    cA
    @5
    cvv
    @0
    f1dom2g
    syl3anc
    exlimddv
    ex
end
