include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "co.mm"
include "clmlmod.mm"
include "lmodvscl.mm"
include "syl3an1.mm"

theorem clmvscl
  let cQ: class Q
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume clmvscl.v: |- V = ( Base ` W )
  assume clmvscl.f: |- F = ( Scalar ` W )
  assume clmvscl.s: |- .x. = ( .s ` W )
  assume clmvscl.k: |- K = ( Base ` F )


  assert |- ( ( W e. CMod /\ Q e. K /\ X e. V ) -> ( Q .x. X ) e. V )

  proof
    cW
    cclm
    wcel
    cW
    clmod
    wcel
    cQ
    cK
    wcel
    cX
    cV
    wcel
    cQ
    cX
    c.x
    co
    cV
    wcel
    cW
    clmlmod
    cQ
    c.x
    cF
    cK
    cV
    cW
    cX
    clmvscl.v
    clmvscl.f
    clmvscl.s
    clmvscl.k
    lmodvscl
    syl3an1
end
