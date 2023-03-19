include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lspsnel5.mm"
include "wb.mm"
include "lspsnel.mm"
include "bitr3d.mm"

theorem lspsnss2
  let wph: wff ph
  let cS: class S
  let c.x: class .x.
  let vk: setvar k
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspsnss2.v: |- V = ( Base ` W )
  assume lspsnss2.s: |- S = ( Scalar ` W )
  assume lspsnss2.k: |- K = ( Base ` S )
  assume lspsnss2.t: |- .x. = ( .s ` W )
  assume lspsnss2.n: |- N = ( LSpan ` W )
  assume lspsnss2.w: |- ( ph -> W e. LMod )
  assume lspsnss2.x: |- ( ph -> X e. V )
  assume lspsnss2.y: |- ( ph -> Y e. V )

  disjoint K k
  disjoint N k
  disjoint S k
  disjoint V k
  disjoint W k
  disjoint X k
  disjoint Y k
  disjoint .x. k
  assert |- ( ph -> ( ( N ` { X } ) C_ ( N ` { Y } ) <-> E. k e. K X = ( k .x. Y ) ) )

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
    cX
    csn
    cN
    cfv
    @0
    wss
    cX
    vk
    cv
    cY
    c.x
    co
    wceq
    vk
    cK
    wrex
    #
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
    lspsnss2.v
    @3
    eqid
    #
    lspsnss2.n
    lspsnss2.w
    wph
    cW
    clmod
    wcel
    #
    cY
    cV
    wcel
    #
    @0
    @3
    wcel
    lspsnss2.w
    lspsnss2.y
    @3
    cN
    cV
    cW
    cY
    lspsnss2.v
    @4
    lspsnss2.n
    lspsncl
    syl2anc
    lspsnss2.x
    lspsnel5
    wph
    @5
    @6
    @1
    @2
    wb
    lspsnss2.w
    lspsnss2.y
    c.x
    cX
    vk
    cS
    cK
    cN
    cV
    cW
    cY
    lspsnss2.s
    lspsnss2.k
    lspsnss2.v
    lspsnss2.t
    lspsnss2.n
    lspsnel
    syl2anc
    bitr3d
end
