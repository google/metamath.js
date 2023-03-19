include "clmod.mm"
include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "clss.mm"
include "co.mm"
include "eqid.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lspsnid.mm"
include "lssvscl.mm"
include "syl22anc.mm"

theorem lspsneli
  let wph: wff ph
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lspsnvsel.v: |- V = ( Base ` W )
  assume lspsnvsel.t: |- .x. = ( .s ` W )
  assume lspsnvsel.f: |- F = ( Scalar ` W )
  assume lspsnvsel.k: |- K = ( Base ` F )
  assume lspsnvsel.n: |- N = ( LSpan ` W )
  assume lspsnvsel.w: |- ( ph -> W e. LMod )
  assume lspsnvsel.a: |- ( ph -> A e. K )
  assume lspsnvsel.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( A .x. X ) e. ( N ` { X } ) )

  proof
    wph
    cW
    clmod
    wcel
    #
    cX
    csn
    cN
    cfv
    #
    cW
    clss
    cfv
    #
    wcel
    #
    cA
    cK
    wcel
    cX
    @1
    wcel
    #
    cA
    cX
    c.x
    co
    @1
    wcel
    lspsnvsel.w
    wph
    @0
    cX
    cV
    wcel
    #
    @3
    lspsnvsel.w
    lspsnvsel.x
    @2
    cN
    cV
    cW
    cX
    lspsnvsel.v
    @2
    eqid
    #
    lspsnvsel.n
    lspsncl
    syl2anc
    lspsnvsel.a
    wph
    @0
    @5
    @4
    lspsnvsel.w
    lspsnvsel.x
    cN
    cV
    cW
    cX
    lspsnvsel.v
    lspsnvsel.n
    lspsnid
    syl2anc
    cK
    @2
    c.x
    @1
    cF
    cW
    cA
    cX
    lspsnvsel.f
    lspsnvsel.t
    lspsnvsel.k
    @6
    lssvscl
    syl22anc
end
