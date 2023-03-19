include "wcel.mm"
include "lssss.mm"
include "sselda.mm"

theorem lssel
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume lssss.v: |- V = ( Base ` W )
  assume lssss.s: |- S = ( LSubSp ` W )


  assert |- ( ( U e. S /\ X e. U ) -> X e. V )

  proof
    cU
    cS
    wcel
    cU
    cV
    cX
    cS
    cU
    cV
    cW
    lssss.v
    lssss.s
    lssss
    sselda
end
