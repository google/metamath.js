include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "wceq.mm"
include "csca.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "wral.mm"
include "csn.mm"
include "cphl.mm"
include "cbs.mm"
include "wss.mm"
include "wa.mm"
include "eqid.mm"
include "isobs.mm"
include "simp3bi.mm"
include "simprd.mm"

theorem obsocv
  let cB: class B
  let c.pe: class ._|_
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume obsocv.z: |- .0. = ( 0g ` W )
  assume obsocv.o: |- ._|_ = ( ocv ` W )


  assert |- ( B e. ( OBasis ` W ) -> ( ._|_ ` B ) = { .0. } )

  proof
    cB
    cW
    cobs
    cfv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cW
    cip
    cfv
    #
    co
    @1
    @2
    wceq
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @4
    c0g
    cfv
    #
    cif
    wceq
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cB
    c.pe
    cfv
    c.0
    csn
    wceq
    #
    @0
    cW
    cphl
    wcel
    cB
    cW
    cbs
    cfv
    #
    wss
    @7
    @8
    wa
    vx
    vy
    cB
    @5
    @4
    @3
    c.pe
    @9
    cW
    c.0
    @6
    @9
    eqid
    @3
    eqid
    @4
    eqid
    @5
    eqid
    @6
    eqid
    obsocv.o
    obsocv.z
    isobs
    simp3bi
    simprd
end
