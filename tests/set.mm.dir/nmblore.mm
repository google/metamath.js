include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "cr.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "cpnf.mm"
include "wf.mm"
include "blof.mm"
include "nmogtmnf.mm"
include "syld3an3.mm"
include "wa.mm"
include "clno.mm"
include "co.mm"
include "eqid.mm"
include "isblo.mm"
include "simplbda.mm"
include "3impa.mm"
include "cxr.mm"
include "wb.mm"
include "nmoxr.mm"
include "xrrebnd.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem nmblore
  let cB: class B
  let cT: class T
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  assume nmblore.1: |- X = ( BaseSet ` U )
  assume nmblore.2: |- Y = ( BaseSet ` W )
  assume nmblore.3: |- N = ( U normOpOLD W )
  assume nmblore.5: |- B = ( U BLnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. B ) -> ( N ` T ) e. RR )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cT
    cB
    wcel
    #
    w3a
    #
    cT
    cN
    cfv
    #
    cr
    wcel
    #
    cmnf
    @4
    clt
    wbr
    #
    @4
    cpnf
    clt
    wbr
    #
    @0
    @1
    @2
    cX
    cY
    cT
    wf
    #
    @6
    cB
    cT
    cU
    cW
    cX
    cY
    nmblore.1
    nmblore.2
    nmblore.5
    blof
    #
    cT
    cU
    cN
    cW
    cX
    cY
    nmblore.1
    nmblore.2
    nmblore.3
    nmogtmnf
    syld3an3
    @0
    @1
    @2
    @7
    @0
    @1
    wa
    @2
    cT
    cU
    cW
    clno
    co
    #
    wcel
    @7
    cB
    cT
    cU
    @10
    cN
    cW
    nmblore.3
    @10
    eqid
    nmblore.5
    isblo
    simplbda
    3impa
    @3
    @4
    cxr
    wcel
    #
    @5
    @6
    @7
    wa
    wb
    @0
    @1
    @2
    @8
    @11
    @9
    cT
    cU
    cN
    cW
    cX
    cY
    nmblore.1
    nmblore.2
    nmblore.3
    nmoxr
    syld3an3
    @4
    xrrebnd
    syl
    mpbir2and
end
