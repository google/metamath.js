include "cnv.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cfv.mm"
include "cr.mm"
include "cpnf.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "nmorepnf.mm"
include "cxr.mm"
include "wceq.mm"
include "wn.mm"
include "wb.mm"
include "nmoxr.mm"
include "nltpnft.mm"
include "syl.mm"
include "necon2abid.mm"
include "bitr4d.mm"

theorem nmoreltpnf
  let cT: class T
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  assume nmoxr.1: |- X = ( BaseSet ` U )
  assume nmoxr.2: |- Y = ( BaseSet ` W )
  assume nmoxr.3: |- N = ( U normOpOLD W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) -> ( ( N ` T ) e. RR <-> ( N ` T ) < +oo ) )

  proof
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    cX
    cY
    cT
    wf
    w3a
    #
    cT
    cN
    cfv
    #
    cr
    wcel
    @1
    cpnf
    wne
    @1
    cpnf
    clt
    wbr
    #
    cT
    cU
    cN
    cW
    cX
    cY
    nmoxr.1
    nmoxr.2
    nmoxr.3
    nmorepnf
    @0
    @2
    @1
    cpnf
    @0
    @1
    cxr
    wcel
    @1
    cpnf
    wceq
    @2
    wn
    wb
    cT
    cU
    cN
    cW
    cX
    cY
    nmoxr.1
    nmoxr.2
    nmoxr.3
    nmoxr
    @1
    nltpnft
    syl
    necon2abid
    bitr4d
end
