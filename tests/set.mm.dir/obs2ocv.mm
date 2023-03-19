include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "c0g.mm"
include "csn.mm"
include "eqid.mm"
include "obsocv.mm"
include "fveq2d.mm"
include "cphl.mm"
include "wceq.mm"
include "obsrcl.mm"
include "ocvz.mm"
include "syl.mm"
include "eqtrd.mm"

theorem obs2ocv
  let cB: class B
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume obs2ocv.o: |- ._|_ = ( ocv ` W )
  assume obs2ocv.v: |- V = ( Base ` W )


  assert |- ( B e. ( OBasis ` W ) -> ( ._|_ ` ( ._|_ ` B ) ) = V )

  proof
    cB
    cW
    cobs
    cfv
    wcel
    #
    cB
    c.pe
    cfv
    #
    c.pe
    cfv
    cW
    c0g
    cfv
    #
    csn
    #
    c.pe
    cfv
    #
    cV
    @0
    @1
    @3
    c.pe
    cB
    c.pe
    cW
    @2
    @2
    eqid
    #
    obs2ocv.o
    obsocv
    fveq2d
    @0
    cW
    cphl
    wcel
    @4
    cV
    wceq
    cB
    cW
    obsrcl
    c.pe
    cV
    cW
    @2
    obs2ocv.v
    obs2ocv.o
    @5
    ocvz
    syl
    eqtrd
end
