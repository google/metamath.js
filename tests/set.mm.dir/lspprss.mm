include "clmod.mm"
include "wcel.mm"
include "cpr.mm"
include "wss.mm"
include "cfv.mm"
include "wa.mm"
include "jca.mm"
include "wb.mm"
include "prssg.mm"
include "syl.mm"
include "mpbid.mm"
include "lspssp.mm"
include "syl3anc.mm"

theorem lspprss
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspprss.s: |- S = ( LSubSp ` W )
  assume lspprss.n: |- N = ( LSpan ` W )
  assume lspprss.w: |- ( ph -> W e. LMod )
  assume lspprss.u: |- ( ph -> U e. S )
  assume lspprss.x: |- ( ph -> X e. U )
  assume lspprss.y: |- ( ph -> Y e. U )


  assert |- ( ph -> ( N ` { X , Y } ) C_ U )

  proof
    wph
    cW
    clmod
    wcel
    cU
    cS
    wcel
    cX
    cY
    cpr
    #
    cU
    wss
    #
    @0
    cN
    cfv
    cU
    wss
    lspprss.w
    lspprss.u
    wph
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    wa
    #
    @1
    wph
    @2
    @3
    lspprss.x
    lspprss.y
    jca
    #
    wph
    @4
    @4
    @1
    wb
    @5
    cX
    cY
    cU
    cU
    cU
    prssg
    syl
    mpbid
    cS
    @0
    cU
    cN
    cW
    lspprss.s
    lspprss.n
    lspssp
    syl3anc
end
