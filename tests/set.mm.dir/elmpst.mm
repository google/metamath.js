include "cop.mm"
include "cv.mm"
include "ccnv.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "cfn.mm"
include "cin.mm"
include "cxp.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cotp.mm"
include "w3a.mm"
include "opelxp.mm"
include "cnveq.mm"
include "id.mm"
include "eqeq12d.mm"
include "elrab.mm"
include "cmdv.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "bitri.mm"
include "elfpw.mm"
include "anbi12i.mm"
include "df-ot.mm"
include "mpstval.mm"
include "eleq12i.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem elmpst
  let cA: class A
  let cD: class D
  let cP: class P
  let cT: class T
  let cE: class E
  let cH: class H
  let cV: class V
  let vd: setvar d
  let vt: setvar t
  assume mpstval.v: |- V = ( mDV ` T )
  assume mpstval.e: |- E = ( mEx ` T )
  assume mpstval.p: |- P = ( mPreSt ` T )


  assert |- ( <. D , H , A >. e. P <-> ( ( D C_ V /\ `' D = D ) /\ ( H C_ E /\ H e. Fin ) /\ A e. E ) )

  proof
    cD
    cH
    cop
    #
    cA
    cop
    #
    vd
    cv
    #
    ccnv
    #
    @2
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
    cfn
    cin
    #
    cxp
    #
    cE
    cxp
    #
    wcel
    #
    cD
    cV
    wss
    #
    cD
    ccnv
    #
    cD
    wceq
    #
    wa
    #
    cH
    cE
    wss
    cH
    cfn
    wcel
    wa
    #
    wa
    #
    cA
    cE
    wcel
    #
    wa
    #
    cD
    cH
    cA
    cotp
    #
    cP
    wcel
    @14
    @15
    @17
    w3a
    @10
    @0
    @8
    wcel
    #
    @17
    wa
    @18
    @0
    cA
    @8
    cE
    opelxp
    @20
    @16
    @17
    @20
    cD
    @6
    wcel
    #
    cH
    @7
    wcel
    #
    wa
    @16
    cD
    cH
    @6
    @7
    opelxp
    @21
    @14
    @22
    @15
    @21
    cD
    @5
    wcel
    #
    @13
    wa
    @14
    @4
    @13
    vd
    cD
    @5
    @2
    cD
    wceq
    #
    @3
    @12
    @2
    cD
    @2
    cD
    cnveq
    @24
    id
    eqeq12d
    elrab
    @23
    @11
    @13
    cD
    cV
    cV
    cT
    cmdv
    cfv
    cvv
    mpstval.v
    cT
    cmdv
    fvex
    eqeltri
    elpw2
    anbi1i
    bitri
    cH
    cE
    elfpw
    anbi12i
    bitri
    anbi1i
    bitri
    @19
    @1
    cP
    @9
    cD
    cH
    cA
    df-ot
    cP
    cT
    cE
    cV
    vd
    mpstval.v
    mpstval.e
    mpstval.p
    mpstval
    eleq12i
    @14
    @15
    @17
    df-3an
    3bitr4i
end
