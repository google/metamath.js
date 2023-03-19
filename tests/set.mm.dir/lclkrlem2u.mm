include "co.mm"
include "cfv.mm"
include "dvhlmod.mm"
include "ldualvaddcom.mm"
include "fveq1d.mm"
include "eqnetrrd.mm"
include "lclkrlem2t.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"

theorem lclkrlem2u
  let wph: wff ph
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
  assume lclkrlem2u.n: |- ( ph -> ( ( E .+ G ) ` X ) =/= .0. )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` ( E .+ G ) ) ) ) = ( L ` ( E .+ G ) ) )

  proof
    wph
    cG
    cE
    c.pl
    co
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    @1
    cE
    cG
    c.pl
    co
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    @4
    wph
    cD
    c.pl
    c.po
    cS
    c.x
    c.xp
    cU
    cG
    cF
    cE
    cH
    cI
    cK
    cL
    c.mi
    cN
    c.pe
    cV
    cW
    cY
    cX
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
    lclkrlem2m.y
    lclkrlem2m.x
    lclkrlem2m.g
    lclkrlem2m.e
    lclkrlem2n.n
    lclkrlem2n.l
    lclkrlem2o.h
    lclkrlem2o.o
    lclkrlem2o.u
    lclkrlem2o.a
    lclkrlem2o.k
    lclkrlem2q.lg
    lclkrlem2q.le
    wph
    cX
    @3
    cfv
    cX
    @0
    cfv
    c.0
    wph
    cX
    @3
    @0
    wph
    cD
    c.pl
    cF
    cU
    cE
    cG
    lclkrlem2m.f
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
    ldualvaddcom
    #
    fveq1d
    lclkrlem2u.n
    eqnetrrd
    lclkrlem2t
    wph
    @5
    @2
    c.pe
    wph
    @4
    @1
    c.pe
    wph
    @3
    @0
    cL
    @6
    fveq2d
    #
    fveq2d
    fveq2d
    @7
    3eqtr4d
end
