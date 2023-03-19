include "chlt.mm"
include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "catm.mm"
include "eqid.mm"
include "pol0N.mm"
include "fveq2d.mm"
include "pol1N.mm"
include "eqtrd.mm"

theorem 2pol0N
  let cK: class K
  let c.pe: class ._|_
  assume 2pol0.o: |- ._|_ = ( _|_P ` K )


  assert |- ( K e. HL -> ( ._|_ ` ( ._|_ ` (/) ) ) = (/) )

  proof
    cK
    chlt
    wcel
    #
    c0
    c.pe
    cfv
    #
    c.pe
    cfv
    cK
    catm
    cfv
    #
    c.pe
    cfv
    c0
    @0
    @1
    @2
    c.pe
    @2
    chlt
    cK
    c.pe
    @2
    eqid
    #
    2pol0.o
    pol0N
    fveq2d
    @2
    cK
    c.pe
    @3
    2pol0.o
    pol1N
    eqtrd
end
