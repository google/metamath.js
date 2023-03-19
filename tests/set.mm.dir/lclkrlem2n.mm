include "clss.mm"
include "cfv.mm"
include "co.mm"
include "eqid.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "ldualvaddcl.mm"
include "lkrlss.mm"
include "syl2anc.mm"
include "wceq.mm"
include "ellkr2.mm"
include "mpbird.mm"
include "lspprss.mm"

theorem lclkrlem2n
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lclkrlem2m.v: |- V = ( Base ` U )
  assume lclkrlem2m.t: |- .x. = ( .s ` U )
  assume lclkrlem2m.s: |- S = ( Scalar ` U )
  assume lclkrlem2m.q: |- .X. = ( .r ` S )
  assume lclkrlem2m.z: |- .0. = ( 0g ` S )
  assume lclkrlem2m.i: |- I = ( invr ` S )
  assume lclkrlem2m.m: |- .- = ( -g ` U )
  assume lclkrlem2m.f: |- F = ( LFnl ` U )
  assume lclkrlem2m.d: |- D = ( LDual ` U )
  assume lclkrlem2m.p: |- .+ = ( +g ` D )
  assume lclkrlem2m.x: |- ( ph -> X e. V )
  assume lclkrlem2m.y: |- ( ph -> Y e. V )
  assume lclkrlem2m.e: |- ( ph -> E e. F )
  assume lclkrlem2m.g: |- ( ph -> G e. F )
  assume lclkrlem2n.n: |- N = ( LSpan ` U )
  assume lclkrlem2n.l: |- L = ( LKer ` U )
  assume lclkrlem2n.w: |- ( ph -> U e. LVec )
  assume lclkrlem2n.j: |- ( ph -> ( ( E .+ G ) ` X ) = .0. )
  assume lclkrlem2n.k: |- ( ph -> ( ( E .+ G ) ` Y ) = .0. )


  assert |- ( ph -> ( N ` { X , Y } ) C_ ( L ` ( E .+ G ) ) )

  proof
    wph
    cU
    clss
    cfv
    #
    cE
    cG
    c.pl
    co
    #
    cL
    cfv
    #
    cN
    cU
    cX
    cY
    @0
    eqid
    #
    lclkrlem2n.n
    wph
    cU
    clvec
    wcel
    cU
    clmod
    wcel
    #
    lclkrlem2n.w
    cU
    lveclmod
    syl
    #
    wph
    @4
    @1
    cF
    wcel
    @2
    @0
    wcel
    @5
    wph
    cD
    c.pl
    cF
    cE
    cG
    cU
    lclkrlem2m.f
    lclkrlem2m.d
    lclkrlem2m.p
    @5
    lclkrlem2m.e
    lclkrlem2m.g
    ldualvaddcl
    #
    @0
    cF
    @1
    cL
    cU
    lclkrlem2m.f
    lclkrlem2n.l
    @3
    lkrlss
    syl2anc
    wph
    cX
    @2
    wcel
    cX
    @1
    cfv
    c.0
    wceq
    lclkrlem2n.j
    wph
    cS
    cF
    @1
    cL
    cV
    cU
    cX
    clvec
    c.0
    lclkrlem2m.v
    lclkrlem2m.s
    lclkrlem2m.z
    lclkrlem2m.f
    lclkrlem2n.l
    lclkrlem2n.w
    @6
    lclkrlem2m.x
    ellkr2
    mpbird
    wph
    cY
    @2
    wcel
    cY
    @1
    cfv
    c.0
    wceq
    lclkrlem2n.k
    wph
    cS
    cF
    @1
    cL
    cV
    cU
    cY
    clvec
    c.0
    lclkrlem2m.v
    lclkrlem2m.s
    lclkrlem2m.z
    lclkrlem2m.f
    lclkrlem2n.l
    lclkrlem2n.w
    @6
    lclkrlem2m.y
    ellkr2
    mpbird
    lspprss
end
