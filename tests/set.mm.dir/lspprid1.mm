include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "clmod.mm"
include "prssi.mm"
include "syl2anc.mm"
include "snsspr1.mm"
include "a1i.mm"
include "lspss.mm"
include "syl3anc.mm"
include "clss.mm"
include "eqid.mm"
include "lspprcl.mm"
include "lspsnel5.mm"
include "mpbird.mm"

theorem lspprid1
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspprid.v: |- V = ( Base ` W )
  assume lspprid.n: |- N = ( LSpan ` W )
  assume lspprid.w: |- ( ph -> W e. LMod )
  assume lspprid.x: |- ( ph -> X e. V )
  assume lspprid.y: |- ( ph -> Y e. V )


  assert |- ( ph -> X e. ( N ` { X , Y } ) )

  proof
    wph
    cX
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    wcel
    cX
    csn
    #
    cN
    cfv
    @1
    wss
    #
    wph
    cW
    clmod
    wcel
    @0
    cV
    wss
    #
    @2
    @0
    wss
    #
    @3
    lspprid.w
    wph
    cX
    cV
    wcel
    cY
    cV
    wcel
    @4
    lspprid.x
    lspprid.y
    cX
    cY
    cV
    prssi
    syl2anc
    @5
    wph
    cX
    cY
    snsspr1
    a1i
    @2
    @0
    cN
    cV
    cW
    lspprid.v
    lspprid.n
    lspss
    syl3anc
    wph
    cW
    clss
    cfv
    #
    @1
    cN
    cV
    cW
    cX
    lspprid.v
    @6
    eqid
    #
    lspprid.n
    lspprid.w
    wph
    @6
    cN
    cV
    cW
    cX
    cY
    lspprid.v
    @7
    lspprid.n
    lspprid.w
    lspprid.x
    lspprid.y
    lspprcl
    lspprid.x
    lspsnel5
    mpbird
end
