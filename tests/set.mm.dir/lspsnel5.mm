include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "lspsnel6.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem lspsnel5
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lspsnel5.v: |- V = ( Base ` W )
  assume lspsnel5.s: |- S = ( LSubSp ` W )
  assume lspsnel5.n: |- N = ( LSpan ` W )
  assume lspsnel5.w: |- ( ph -> W e. LMod )
  assume lspsnel5.a: |- ( ph -> U e. S )
  assume lspsnel5.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( X e. U <-> ( N ` { X } ) C_ U ) )

  proof
    wph
    cX
    cU
    wcel
    cX
    cV
    wcel
    #
    cX
    csn
    cN
    cfv
    cU
    wss
    #
    wa
    @1
    wph
    cS
    cU
    cN
    cV
    cW
    cX
    lspsnel5.v
    lspsnel5.s
    lspsnel5.n
    lspsnel5.w
    lspsnel5.a
    lspsnel6
    wph
    @0
    @1
    lspsnel5.x
    biantrurd
    bitr4d
end
