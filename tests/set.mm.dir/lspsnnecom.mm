include "csn.mm"
include "cfv.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "eldifad.mm"
include "lspsnne2.mm"
include "necomd.mm"
include "lspsnne1.mm"

theorem lspsnnecom
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspsnnecom.v: |- V = ( Base ` W )
  assume lspsnnecom.o: |- .0. = ( 0g ` W )
  assume lspsnnecom.n: |- N = ( LSpan ` W )
  assume lspsnnecom.w: |- ( ph -> W e. LVec )
  assume lspsnnecom.x: |- ( ph -> X e. V )
  assume lspsnnecom.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lspsnnecom.e: |- ( ph -> -. X e. ( N ` { Y } ) )


  assert |- ( ph -> -. Y e. ( N ` { X } ) )

  proof
    wph
    cN
    cV
    cW
    cY
    cX
    c.0
    lspsnnecom.v
    lspsnnecom.o
    lspsnnecom.n
    lspsnnecom.w
    lspsnnecom.y
    lspsnnecom.x
    wph
    cX
    csn
    cN
    cfv
    cY
    csn
    cN
    cfv
    wph
    cN
    cV
    cW
    cX
    cY
    lspsnnecom.v
    lspsnnecom.n
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    lspsnnecom.w
    cW
    lveclmod
    syl
    lspsnnecom.x
    wph
    cY
    cV
    c.0
    csn
    lspsnnecom.y
    eldifad
    lspsnnecom.e
    lspsnne2
    necomd
    lspsnne1
end
