include "co.mm"
include "csn.mm"
include "cfv.mm"
include "clsm.mm"
include "cpr.mm"
include "csubg.mm"
include "wcel.mm"
include "clmod.mm"
include "lspsnsubg.mm"
include "syl2anc.mm"
include "lspsneli.mm"
include "eqid.mm"
include "lsmelvali.mm"
include "syl22anc.mm"
include "lsmpr.mm"
include "eleqtrrd.mm"

theorem lsppreli
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lsppreli.v: |- V = ( Base ` W )
  assume lsppreli.p: |- .+ = ( +g ` W )
  assume lsppreli.t: |- .x. = ( .s ` W )
  assume lsppreli.f: |- F = ( Scalar ` W )
  assume lsppreli.k: |- K = ( Base ` F )
  assume lsppreli.n: |- N = ( LSpan ` W )
  assume lsppreli.w: |- ( ph -> W e. LMod )
  assume lsppreli.a: |- ( ph -> A e. K )
  assume lsppreli.b: |- ( ph -> B e. K )
  assume lsppreli.x: |- ( ph -> X e. V )
  assume lsppreli.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( ( A .x. X ) .+ ( B .x. Y ) ) e. ( N ` { X , Y } ) )

  proof
    wph
    cA
    cX
    c.x
    co
    #
    cB
    cY
    c.x
    co
    #
    c.pl
    co
    #
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    cW
    clsm
    cfv
    #
    co
    #
    cX
    cY
    cpr
    cN
    cfv
    wph
    @3
    cW
    csubg
    cfv
    #
    wcel
    #
    @4
    @7
    wcel
    #
    @0
    @3
    wcel
    @1
    @4
    wcel
    @2
    @6
    wcel
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    @8
    lsppreli.w
    lsppreli.x
    cN
    cV
    cW
    cX
    lsppreli.v
    lsppreli.n
    lspsnsubg
    syl2anc
    wph
    @10
    cY
    cV
    wcel
    @9
    lsppreli.w
    lsppreli.y
    cN
    cV
    cW
    cY
    lsppreli.v
    lsppreli.n
    lspsnsubg
    syl2anc
    wph
    cA
    c.x
    cF
    cK
    cN
    cV
    cW
    cX
    lsppreli.v
    lsppreli.t
    lsppreli.f
    lsppreli.k
    lsppreli.n
    lsppreli.w
    lsppreli.a
    lsppreli.x
    lspsneli
    wph
    cB
    c.x
    cF
    cK
    cN
    cV
    cW
    cY
    lsppreli.v
    lsppreli.t
    lsppreli.f
    lsppreli.k
    lsppreli.n
    lsppreli.w
    lsppreli.b
    lsppreli.y
    lspsneli
    c.pl
    @5
    @3
    @4
    cW
    @0
    @1
    lsppreli.p
    @5
    eqid
    #
    lsmelvali
    syl22anc
    wph
    @5
    cN
    cV
    cW
    cX
    cY
    lsppreli.v
    lsppreli.n
    @11
    lsppreli.w
    lsppreli.x
    lsppreli.y
    lsmpr
    eleqtrrd
end
