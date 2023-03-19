include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "bloval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isblo
  let cB: class B
  let cT: class T
  let cU: class U
  let cL: class L
  let cN: class N
  let cW: class W
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  assume bloval.3: |- N = ( U normOpOLD W )
  assume bloval.4: |- L = ( U LnOp W )
  assume bloval.5: |- B = ( U BLnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> ( T e. B <-> ( T e. L /\ ( N ` T ) < +oo ) ) )

  proof
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    wa
    #
    cT
    cB
    wcel
    cT
    vt
    cv
    #
    cN
    cfv
    #
    cpnf
    clt
    wbr
    #
    vt
    cL
    crab
    #
    wcel
    cT
    cL
    wcel
    cT
    cN
    cfv
    #
    cpnf
    clt
    wbr
    #
    wa
    @0
    cB
    @4
    cT
    vt
    cB
    cU
    cL
    cN
    cW
    bloval.3
    bloval.4
    bloval.5
    bloval
    eleq2d
    @3
    @6
    vt
    cT
    cL
    @1
    cT
    wceq
    @2
    @5
    cpnf
    clt
    @1
    cT
    cN
    fveq2
    breq1d
    elrab
    syl6bb
end
