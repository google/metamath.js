include "wcel.mm"
include "clmod.mm"
include "csn.mm"
include "wss.mm"
include "cfv.mm"
include "snssi.mm"
include "lspcl.mm"
include "sylan2.mm"

theorem lspsncl
  let cS: class S
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vp: setvar p
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cU: class U
  assume lspval.v: |- V = ( Base ` W )
  assume lspval.s: |- S = ( LSubSp ` W )
  assume lspval.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ X e. V ) -> ( N ` { X } ) e. S )

  proof
    cX
    cV
    wcel
    cW
    clmod
    wcel
    cX
    csn
    #
    cV
    wss
    @0
    cN
    cfv
    cS
    wcel
    cX
    cV
    snssi
    cS
    @0
    cN
    cV
    cW
    lspval.v
    lspval.s
    lspval.n
    lspcl
    sylan2
end
