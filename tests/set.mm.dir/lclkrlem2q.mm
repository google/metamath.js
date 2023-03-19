include "clsh.mm"
include "cfv.mm"
include "c0g.mm"
include "eqid.mm"
include "wcel.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "co.mm"
include "wceq.mm"
include "dvhlvec.mm"
include "lclkrlem2m.mm"
include "simpld.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simprd.mm"
include "lclkrlem2o.mm"
include "lclkrlem2l.mm"

theorem lclkrlem2q
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
  assume lclkrlem2q.bn: |- ( ph -> B =/= ( 0g ` U ) )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` ( E .+ G ) ) ) ) = ( L ` ( E .+ G ) ) )

  proof
    wph
    cB
    cD
    c.pl
    c.po
    c.0
    cS
    cU
    cE
    cF
    cG
    cH
    cU
    clsh
    cfv
    #
    cK
    cL
    cN
    c.pe
    cV
    cW
    cX
    cY
    cU
    c0g
    cfv
    #
    lclkrlem2o.h
    lclkrlem2o.o
    lclkrlem2o.u
    lclkrlem2m.v
    lclkrlem2m.s
    lclkrlem2m.z
    @1
    eqid
    lclkrlem2o.a
    lclkrlem2n.n
    lclkrlem2m.f
    @0
    eqid
    lclkrlem2n.l
    lclkrlem2m.d
    lclkrlem2m.p
    lclkrlem2o.k
    wph
    cB
    cV
    wcel
    #
    cB
    @1
    wne
    cB
    cV
    @1
    csn
    cdif
    wcel
    wph
    @2
    cB
    cE
    cG
    c.pl
    co
    cfv
    c.0
    wceq
    #
    wph
    cB
    cD
    c.pl
    cS
    c.x
    c.xp
    cU
    cE
    cF
    cG
    cI
    c.mi
    cV
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
    wph
    cU
    cH
    cK
    cW
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2o.k
    dvhlvec
    lclkrlem2q.b
    lclkrlem2q.n
    lclkrlem2m
    #
    simpld
    lclkrlem2q.bn
    cB
    cV
    @1
    eldifsn
    sylanbrc
    lclkrlem2m.e
    lclkrlem2m.g
    lclkrlem2q.le
    lclkrlem2q.lg
    wph
    @2
    @3
    @4
    simprd
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
    lclkrlem2q.bn
    lclkrlem2o
    lclkrlem2m.x
    lclkrlem2m.y
    lclkrlem2l
end
