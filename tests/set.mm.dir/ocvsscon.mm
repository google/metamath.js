include "cphl.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "ocvocv.mm"
include "3adant2.mm"
include "ocv2ss.mm"
include "sstr2.mm"
include "syl2im.mm"
include "3adant3.mm"
include "impbid.mm"

theorem ocvsscon
  let cS: class S
  let cT: class T
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume ocvlsp.v: |- V = ( Base ` W )
  assume ocvlsp.o: |- ._|_ = ( ocv ` W )


  assert |- ( ( W e. PreHil /\ S C_ V /\ T C_ V ) -> ( S C_ ( ._|_ ` T ) <-> T C_ ( ._|_ ` S ) ) )

  proof
    cW
    cphl
    wcel
    #
    cS
    cV
    wss
    #
    cT
    cV
    wss
    #
    w3a
    #
    cS
    cT
    c.pe
    cfv
    #
    wss
    #
    cT
    cS
    c.pe
    cfv
    #
    wss
    #
    @3
    cT
    @4
    c.pe
    cfv
    #
    wss
    #
    @5
    @8
    @6
    wss
    @7
    @0
    @2
    @9
    @1
    cT
    c.pe
    cV
    cW
    ocvlsp.v
    ocvlsp.o
    ocvocv
    3adant2
    @4
    cS
    c.pe
    cW
    ocvlsp.o
    ocv2ss
    cT
    @8
    @6
    sstr2
    syl2im
    @3
    cS
    @6
    c.pe
    cfv
    #
    wss
    #
    @7
    @10
    @4
    wss
    @5
    @0
    @1
    @11
    @2
    cS
    c.pe
    cV
    cW
    ocvlsp.v
    ocvlsp.o
    ocvocv
    3adant3
    @6
    cT
    c.pe
    cW
    ocvlsp.o
    ocv2ss
    cS
    @10
    @4
    sstr2
    syl2im
    impbid
end
