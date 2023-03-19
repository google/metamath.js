include "cnv.mm"
include "wcel.mm"
include "clno.mm"
include "co.mm"
include "wf.mm"
include "eqid.mm"
include "bloln.mm"
include "lnof.mm"
include "syld3an3.mm"

theorem blof
  let cB: class B
  let cT: class T
  let cU: class U
  let cW: class W
  let cX: class X
  let cY: class Y
  assume blof.1: |- X = ( BaseSet ` U )
  assume blof.2: |- Y = ( BaseSet ` W )
  assume blof.5: |- B = ( U BLnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. B ) -> T : X --> Y )

  proof
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    cT
    cB
    wcel
    cT
    cU
    cW
    clno
    co
    #
    wcel
    cX
    cY
    cT
    wf
    cB
    cT
    cU
    @0
    cW
    @0
    eqid
    #
    blof.5
    bloln
    cT
    cU
    @0
    cW
    cX
    cY
    blof.1
    blof.2
    @1
    lnof
    syld3an3
end
