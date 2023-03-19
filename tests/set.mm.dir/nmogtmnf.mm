include "cnv.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cfv.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "wn.mm"
include "wb.mm"
include "wo.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "wne.mm"
include "nmorepnf.mm"
include "df-ne.mm"
include "syl6bb.mm"
include "xor3.mm"
include "nbior.mm"
include "sylbir.mm"
include "mnfltxr.mm"
include "3syl.mm"

theorem nmogtmnf
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


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) -> -oo < ( N ` T ) )

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
    #
    @1
    cpnf
    wceq
    #
    wn
    #
    wb
    #
    @2
    @3
    wo
    #
    cmnf
    @1
    clt
    wbr
    @0
    @2
    @1
    cpnf
    wne
    @4
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
    @1
    cpnf
    df-ne
    syl6bb
    @5
    @2
    @3
    wb
    wn
    @6
    @2
    @3
    xor3
    @2
    @3
    nbior
    sylbir
    @1
    mnfltxr
    3syl
end
