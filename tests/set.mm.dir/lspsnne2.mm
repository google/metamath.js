include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "wss.mm"
include "eqimss.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lspsnel5.mm"
include "syl5ibr.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem lspsnne2
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspsnne2.v: |- V = ( Base ` W )
  assume lspsnne2.n: |- N = ( LSpan ` W )
  assume lspsnne2.w: |- ( ph -> W e. LMod )
  assume lspsnne2.x: |- ( ph -> X e. V )
  assume lspsnne2.y: |- ( ph -> Y e. V )
  assume lspsnne2.e: |- ( ph -> -. X e. ( N ` { Y } ) )


  assert |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )

  proof
    wph
    cX
    cY
    csn
    cN
    cfv
    #
    wcel
    #
    wn
    cX
    csn
    cN
    cfv
    #
    @0
    wne
    lspsnne2.e
    wph
    @1
    @2
    @0
    @2
    @0
    wceq
    @1
    wph
    @2
    @0
    wss
    @2
    @0
    eqimss
    wph
    cW
    clss
    cfv
    #
    @0
    cN
    cV
    cW
    cX
    lspsnne2.v
    @3
    eqid
    #
    lspsnne2.n
    lspsnne2.w
    wph
    cW
    clmod
    wcel
    cY
    cV
    wcel
    @0
    @3
    wcel
    lspsnne2.w
    lspsnne2.y
    @3
    cN
    cV
    cW
    cY
    lspsnne2.v
    @4
    lspsnne2.n
    lspsncl
    syl2anc
    lspsnne2.x
    lspsnel5
    syl5ibr
    necon3bd
    mpd
end
