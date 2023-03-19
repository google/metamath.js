include "cphl.mm"
include "wcel.mm"
include "c0.mm"
include "cocv.mm"
include "cfv.mm"
include "eqid.mm"
include "ocv0.mm"
include "wss.mm"
include "0ss.mm"
include "ocvcss.mm"
include "mpan2.mm"
include "syl5eqelr.mm"

theorem css1
  let cC: class C
  let cV: class V
  let cW: class W
  assume css1.v: |- V = ( Base ` W )
  assume css1.c: |- C = ( CSubSp ` W )


  assert |- ( W e. PreHil -> V e. C )

  proof
    cW
    cphl
    wcel
    #
    cV
    c0
    cW
    cocv
    cfv
    #
    cfv
    #
    cC
    @1
    cV
    cW
    css1.v
    @1
    eqid
    #
    ocv0
    @0
    c0
    cV
    wss
    @2
    cC
    wcel
    cV
    0ss
    cC
    c0
    @1
    cV
    cW
    css1.v
    css1.c
    @3
    ocvcss
    mpan2
    syl5eqelr
end
