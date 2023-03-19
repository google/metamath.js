include "cnv.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cdm.mm"
include "crab.mm"
include "wa.mm"
include "hmoval.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem ishmo
  let cA: class A
  let cT: class T
  let cU: class U
  let cH: class H
  let vt: setvar t
  let vu: setvar u
  assume hmoval.8: |- H = ( HmOp ` U )
  assume hmoval.9: |- A = ( U adj U )


  assert |- ( U e. NrmCVec -> ( T e. H <-> ( T e. dom A /\ ( A ` T ) = T ) ) )

  proof
    cU
    cnv
    wcel
    #
    cT
    cH
    wcel
    cT
    vt
    cv
    #
    cA
    cfv
    #
    @1
    wceq
    #
    vt
    cA
    cdm
    #
    crab
    #
    wcel
    cT
    @4
    wcel
    cT
    cA
    cfv
    #
    cT
    wceq
    #
    wa
    @0
    cH
    @5
    cT
    vt
    cA
    cU
    cH
    hmoval.8
    hmoval.9
    hmoval
    eleq2d
    @3
    @7
    vt
    cT
    @4
    @1
    cT
    wceq
    #
    @2
    @6
    @1
    cT
    @1
    cT
    cA
    fveq2
    @8
    id
    eqeq12d
    elrab
    syl6bb
end
