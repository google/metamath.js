include "csn.mm"
include "cfv.mm"
include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "lspsnss.mm"
include "syl3anc.mm"
include "sseldd.mm"

theorem lspsnel3
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspsnss.s: |- S = ( LSubSp ` W )
  assume lspsnss.n: |- N = ( LSpan ` W )
  assume lspsnel3.w: |- ( ph -> W e. LMod )
  assume lspsnel3.u: |- ( ph -> U e. S )
  assume lspsnel3.x: |- ( ph -> X e. U )
  assume lspsnel3.y: |- ( ph -> Y e. ( N ` { X } ) )


  assert |- ( ph -> Y e. U )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cU
    cY
    wph
    cW
    clmod
    wcel
    cU
    cS
    wcel
    cX
    cU
    wcel
    @0
    cU
    wss
    lspsnel3.w
    lspsnel3.u
    lspsnel3.x
    cS
    cU
    cN
    cW
    cX
    lspsnss.s
    lspsnss.n
    lspsnss
    syl3anc
    lspsnel3.y
    sseldd
end
