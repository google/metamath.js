include "cmpst.mm"
include "cfv.mm"
include "cv.mm"
include "ccnv.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "cfn.mm"
include "cin.mm"
include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "cmdv.mm"
include "cmex.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "rabeqdv.mm"
include "ineq1d.mm"
include "xpeq12d.mm"
include "df-mpst.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "rabex.mm"
include "inex1.mm"
include "xpex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "xp0.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "xpeq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mpstval
  let cP: class P
  let cT: class T
  let cE: class E
  let cV: class V
  let vd: setvar d
  let cD: class D
  let vt: setvar t
  assume mpstval.v: |- V = ( mDV ` T )
  assume mpstval.e: |- E = ( mEx ` T )
  assume mpstval.p: |- P = ( mPreSt ` T )

  disjoint T d
  disjoint V d
  disjoint D d
  disjoint E t
  disjoint d t
  disjoint T t
  disjoint V t
  assert |- P = ( ( { d e. ~P V | `' d = d } X. ( ~P E i^i Fin ) ) X. E )

  proof
    cP
    cT
    cmpst
    cfv
    #
    vd
    cv
    #
    ccnv
    @1
    wceq
    #
    vd
    cV
    cpw
    #
    crab
    #
    cE
    cpw
    #
    cfn
    cin
    #
    cxp
    #
    cE
    cxp
    #
    mpstval.p
    cT
    cvv
    wcel
    #
    @0
    @8
    wceq
    vt
    cT
    @2
    vd
    vt
    cv
    #
    cmdv
    cfv
    #
    cpw
    #
    crab
    #
    @10
    cmex
    cfv
    #
    cpw
    #
    cfn
    cin
    #
    cxp
    #
    @14
    cxp
    @8
    cvv
    cmpst
    @10
    cT
    wceq
    #
    @17
    @7
    @14
    cE
    @18
    @13
    @4
    @16
    @6
    @18
    @2
    vd
    @12
    @3
    @18
    @11
    cV
    @18
    @11
    cT
    cmdv
    cfv
    #
    cV
    @10
    cT
    cmdv
    fveq2
    mpstval.v
    syl6eqr
    pweqd
    rabeqdv
    @18
    @15
    @5
    cfn
    @18
    @14
    cE
    @18
    @14
    cT
    cmex
    cfv
    #
    cE
    @10
    cT
    cmex
    fveq2
    mpstval.e
    syl6eqr
    #
    pweqd
    ineq1d
    xpeq12d
    @21
    xpeq12d
    vt
    vd
    df-mpst
    @7
    cE
    @4
    @6
    @2
    vd
    @3
    cV
    cV
    @19
    cvv
    mpstval.v
    cT
    cmdv
    fvex
    eqeltri
    pwex
    rabex
    @5
    cfn
    cE
    cE
    @20
    cvv
    mpstval.e
    cT
    cmex
    fvex
    eqeltri
    #
    pwex
    inex1
    xpex
    @22
    xpex
    fvmpt
    @9
    wn
    #
    c0
    @7
    c0
    cxp
    #
    @0
    @8
    @24
    c0
    @7
    xp0
    eqcomi
    cT
    cmpst
    fvprc
    @23
    cE
    c0
    @7
    @23
    cE
    @20
    c0
    mpstval.e
    cT
    cmex
    fvprc
    syl5eq
    xpeq2d
    3eqtr4a
    pm2.61i
    eqtri
end
