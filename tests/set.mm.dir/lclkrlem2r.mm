include "cfv.mm"
include "cin.mm"
include "co.mm"
include "wss.mm"
include "wceq.mm"
include "csn.mm"
include "lclkrlem2p.mm"
include "3sstr4d.mm"
include "sseqin2.mm"
include "sylib.mm"
include "dvhlmod.mm"
include "lkrin.mm"
include "eqsstr3d.mm"

theorem lclkrlem2r
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.po: class .(+)
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
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
  assume lclkrlem2o.h: |- H = ( LHyp ` K )
  assume lclkrlem2o.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem2o.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem2o.a: |- .(+) = ( LSSum ` U )
  assume lclkrlem2o.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem2q.le: |- ( ph -> ( L ` E ) = ( ._|_ ` { X } ) )
  assume lclkrlem2q.lg: |- ( ph -> ( L ` G ) = ( ._|_ ` { Y } ) )
  assume lclkrlem2q.b: |- B = ( X .- ( ( ( ( E .+ G ) ` X ) .X. ( I ` ( ( E .+ G ) ` Y ) ) ) .x. Y ) )
  assume lclkrlem2q.n: |- ( ph -> ( ( E .+ G ) ` Y ) =/= .0. )
  assume lclkrlem2r.bn: |- ( ph -> B = ( 0g ` U ) )


  assert |- ( ph -> ( L ` G ) C_ ( L ` ( E .+ G ) ) )

  proof
    wph
    cG
    cL
    cfv
    #
    cE
    cL
    cfv
    #
    @0
    cin
    #
    cE
    cG
    c.pl
    co
    cL
    cfv
    wph
    @0
    @1
    wss
    @2
    @0
    wceq
    wph
    cY
    csn
    c.pe
    cfv
    cX
    csn
    c.pe
    cfv
    @0
    @1
    wph
    cB
    cD
    c.pl
    c.po
    cS
    c.x
    c.xp
    cU
    cE
    cF
    cG
    cH
    cI
    cK
    cL
    c.mi
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lclkrlem2m.v
    lclkrlem2m.t
    lclkrlem2m.s
    lclkrlem2m.q
    lclkrlem2m.z
    lclkrlem2m.i
    lclkrlem2m.m
    lclkrlem2m.f
    lclkrlem2m.d
    lclkrlem2m.p
    lclkrlem2m.x
    lclkrlem2m.y
    lclkrlem2m.e
    lclkrlem2m.g
    lclkrlem2n.n
    lclkrlem2n.l
    lclkrlem2o.h
    lclkrlem2o.o
    lclkrlem2o.u
    lclkrlem2o.a
    lclkrlem2o.k
    lclkrlem2q.b
    lclkrlem2q.n
    lclkrlem2r.bn
    lclkrlem2p
    lclkrlem2q.lg
    lclkrlem2q.le
    3sstr4d
    @0
    @1
    sseqin2
    sylib
    wph
    cD
    c.pl
    cF
    cE
    cG
    cL
    cU
    lclkrlem2m.f
    lclkrlem2n.l
    lclkrlem2m.d
    lclkrlem2m.p
    wph
    cU
    cH
    cK
    cW
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2o.k
    dvhlmod
    lclkrlem2m.e
    lclkrlem2m.g
    lkrin
    eqsstr3d
end
