include "cnzr.mm"
include "wcel.mm"
include "crg.mm"
include "c2o.mm"
include "cbs.mm"
include "cfv.mm"
include "cdom.mm"
include "wbr.mm"
include "nzrring.mm"
include "opprring.mm"
include "syl.mm"
include "eqid.mm"
include "isnzr2.mm"
include "simprbi.mm"
include "opprbas.mm"
include "sylanbrc.mm"

theorem opprnzr
  let cR: class R
  let cO: class O
  assume opprnzr.1: |- O = ( oppR ` R )


  assert |- ( R e. NzRing -> O e. NzRing )

  proof
    cR
    cnzr
    wcel
    #
    cO
    crg
    wcel
    #
    c2o
    cR
    cbs
    cfv
    #
    cdom
    wbr
    #
    cO
    cnzr
    wcel
    @0
    cR
    crg
    wcel
    #
    @1
    cR
    nzrring
    cR
    cO
    opprnzr.1
    opprring
    syl
    @0
    @4
    @3
    @2
    cR
    @2
    eqid
    #
    isnzr2
    simprbi
    @2
    cO
    @2
    cR
    cO
    opprnzr.1
    @5
    opprbas
    isnzr2
    sylanbrc
end
