include "cphl.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "ocvocv.mm"
include "ocv2ss.mm"
include "syl.mm"
include "wb.mm"
include "ocvss.mm"
include "a1i.mm"
include "iscss2.mm"
include "sylan2.mm"
include "mpbird.mm"

theorem ocvcss
  let cC: class C
  let cS: class S
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume cssss.v: |- V = ( Base ` W )
  assume cssss.c: |- C = ( CSubSp ` W )
  assume ocvcss.o: |- ._|_ = ( ocv ` W )


  assert |- ( ( W e. PreHil /\ S C_ V ) -> ( ._|_ ` S ) e. C )

  proof
    cW
    cphl
    wcel
    #
    cS
    cV
    wss
    #
    wa
    #
    cS
    c.pe
    cfv
    #
    cC
    wcel
    #
    @3
    c.pe
    cfv
    #
    c.pe
    cfv
    @3
    wss
    #
    @2
    cS
    @5
    wss
    @6
    cS
    c.pe
    cV
    cW
    cssss.v
    ocvcss.o
    ocvocv
    @5
    cS
    c.pe
    cW
    ocvcss.o
    ocv2ss
    syl
    @1
    @0
    @3
    cV
    wss
    #
    @4
    @6
    wb
    @7
    @1
    cS
    c.pe
    cV
    cW
    cssss.v
    ocvcss.o
    ocvss
    a1i
    cC
    @3
    c.pe
    cV
    cW
    cssss.v
    cssss.c
    ocvcss.o
    iscss2
    sylan2
    mpbird
end
