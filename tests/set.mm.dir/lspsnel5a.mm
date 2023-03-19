include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "cbs.mm"
include "eqid.mm"
include "lssel.mm"
include "syl2anc.mm"
include "lspsnel5.mm"
include "mpbid.mm"

theorem lspsnel5a
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  assume lspsnel5a.s: |- S = ( LSubSp ` W )
  assume lspsnel5a.n: |- N = ( LSpan ` W )
  assume lspsnel5a.w: |- ( ph -> W e. LMod )
  assume lspsnel5a.a: |- ( ph -> U e. S )
  assume lspsnel5a.x: |- ( ph -> X e. U )


  assert |- ( ph -> ( N ` { X } ) C_ U )

  proof
    wph
    cX
    cU
    wcel
    #
    cX
    csn
    cN
    cfv
    cU
    wss
    lspsnel5a.x
    wph
    cS
    cU
    cN
    cW
    cbs
    cfv
    #
    cW
    cX
    @1
    eqid
    #
    lspsnel5a.s
    lspsnel5a.n
    lspsnel5a.w
    lspsnel5a.a
    wph
    cU
    cS
    wcel
    @0
    cX
    @1
    wcel
    lspsnel5a.a
    lspsnel5a.x
    cS
    cU
    @1
    cW
    cX
    @2
    lspsnel5a.s
    lssel
    syl2anc
    lspsnel5
    mpbid
end
