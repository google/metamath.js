include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wne.mm"
include "wss.mm"
include "clss.mm"
include "eqid.mm"
include "clvec.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "eldifad.mm"
include "lspsnel5.mm"
include "notbid.mm"
include "lspsncmp.mm"
include "necon3bbid.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem lspsnne1
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspsnne1.v: |- V = ( Base ` W )
  assume lspsnne1.o: |- .0. = ( 0g ` W )
  assume lspsnne1.n: |- N = ( LSpan ` W )
  assume lspsnne1.w: |- ( ph -> W e. LVec )
  assume lspsnne1.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lspsnne1.y: |- ( ph -> Y e. V )
  assume lspsnne1.e: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )


  assert |- ( ph -> -. X e. ( N ` { Y } ) )

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
    #
    cX
    csn
    cN
    cfv
    #
    @0
    wne
    #
    lspsnne1.e
    wph
    @2
    @3
    @0
    wss
    #
    wn
    @4
    wph
    @1
    @5
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
    lspsnne1.v
    @6
    eqid
    #
    lspsnne1.n
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    #
    lspsnne1.w
    cW
    lveclmod
    syl
    #
    wph
    @8
    cY
    cV
    wcel
    @0
    @6
    wcel
    @9
    lspsnne1.y
    @6
    cN
    cV
    cW
    cY
    lspsnne1.v
    @7
    lspsnne1.n
    lspsncl
    syl2anc
    wph
    cX
    cV
    c.0
    csn
    lspsnne1.x
    eldifad
    lspsnel5
    notbid
    wph
    @5
    @3
    @0
    wph
    cN
    cV
    cW
    cX
    cY
    c.0
    lspsnne1.v
    lspsnne1.o
    lspsnne1.n
    lspsnne1.w
    lspsnne1.x
    lspsnne1.y
    lspsncmp
    necon3bbid
    bitrd
    mpbird
end
