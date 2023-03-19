include "wcel.mm"
include "clmod.mm"
include "csn.mm"
include "wss.mm"
include "cfv.mm"
include "snssi.mm"
include "lspssp.mm"
include "syl3an3.mm"

theorem lspsnss
  let cS: class S
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  assume lspsnss.s: |- S = ( LSubSp ` W )
  assume lspsnss.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ U e. S /\ X e. U ) -> ( N ` { X } ) C_ U )

  proof
    cX
    cU
    wcel
    cW
    clmod
    wcel
    cU
    cS
    wcel
    cX
    csn
    #
    cU
    wss
    @0
    cN
    cfv
    cU
    wss
    cX
    cU
    snssi
    cS
    @0
    cU
    cN
    cW
    lspsnss.s
    lspsnss.n
    lspssp
    syl3an3
end
