include "wcel.mm"
include "cocv.mm"
include "cfv.mm"
include "eqid.mm"
include "cssi.mm"
include "ocvss.mm"
include "syl6eqss.mm"

theorem cssss
  let cC: class C
  let cS: class S
  let cV: class V
  let cW: class W
  assume cssss.v: |- V = ( Base ` W )
  assume cssss.c: |- C = ( CSubSp ` W )


  assert |- ( S e. C -> S C_ V )

  proof
    cS
    cC
    wcel
    cS
    cS
    cW
    cocv
    cfv
    #
    cfv
    #
    @0
    cfv
    cV
    cC
    cS
    @0
    cW
    @0
    eqid
    #
    cssss.c
    cssi
    @1
    @0
    cV
    cW
    cssss.v
    @2
    ocvss
    syl6eqss
end
