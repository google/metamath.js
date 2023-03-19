include "co.mm"
include "cfv.mm"
include "dvhlmod.mm"
include "ldualvaddcom.mm"
include "fveq1d.mm"
include "eqtr3d.mm"
include "csn.mm"
include "wcel.mm"
include "wn.mm"
include "orcomd.mm"
include "lclkrlem2j.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"

theorem lclkrlem2k
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.po: class .(+)
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lclkrlem2f.h: |- H = ( LHyp ` K )
  assume lclkrlem2f.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem2f.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem2f.v: |- V = ( Base ` U )
  assume lclkrlem2f.s: |- S = ( Scalar ` U )
  assume lclkrlem2f.q: |- Q = ( 0g ` S )
  assume lclkrlem2f.z: |- .0. = ( 0g ` U )
  assume lclkrlem2f.a: |- .(+) = ( LSSum ` U )
  assume lclkrlem2f.n: |- N = ( LSpan ` U )
  assume lclkrlem2f.f: |- F = ( LFnl ` U )
  assume lclkrlem2f.j: |- J = ( LSHyp ` U )
  assume lclkrlem2f.l: |- L = ( LKer ` U )
  assume lclkrlem2f.d: |- D = ( LDual ` U )
  assume lclkrlem2f.p: |- .+ = ( +g ` D )
  assume lclkrlem2f.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem2f.b: |- ( ph -> B e. ( V \ { .0. } ) )
  assume lclkrlem2f.e: |- ( ph -> E e. F )
  assume lclkrlem2f.g: |- ( ph -> G e. F )
  assume lclkrlem2f.le: |- ( ph -> ( L ` E ) = ( ._|_ ` { X } ) )
  assume lclkrlem2f.lg: |- ( ph -> ( L ` G ) = ( ._|_ ` { Y } ) )
  assume lclkrlem2f.kb: |- ( ph -> ( ( E .+ G ) ` B ) = Q )
  assume lclkrlem2f.nx: |- ( ph -> ( -. X e. ( ._|_ ` { B } ) \/ -. Y e. ( ._|_ ` { B } ) ) )
  assume lclkrlem2k.x: |- ( ph -> X = .0. )
  assume lclkrlem2k.y: |- ( ph -> Y e. V )


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
    cB
    cD
    c.pl
    c.po
    cQ
    cS
    cU
    cG
    cF
    cE
    cH
    cJ
    cK
    cL
    cN
    c.pe
    cV
    cW
    cY
    cX
    c.0
    lclkrlem2f.h
    lclkrlem2f.o
    lclkrlem2f.u
    lclkrlem2f.v
    lclkrlem2f.s
    lclkrlem2f.q
    lclkrlem2f.z
    lclkrlem2f.a
    lclkrlem2f.n
    lclkrlem2f.f
    lclkrlem2f.j
    lclkrlem2f.l
    lclkrlem2f.d
    lclkrlem2f.p
    lclkrlem2f.k
    lclkrlem2f.b
    lclkrlem2f.g
    lclkrlem2f.e
    lclkrlem2f.lg
    lclkrlem2f.le
    wph
    cB
    @3
    cfv
    cB
    @0
    cfv
    cQ
    wph
    cB
    @3
    @0
    wph
    cD
    c.pl
    cF
    cU
    cE
    cG
    lclkrlem2f.f
    lclkrlem2f.d
    lclkrlem2f.p
    wph
    cU
    cH
    cK
    cW
    lclkrlem2f.h
    lclkrlem2f.u
    lclkrlem2f.k
    dvhlmod
    lclkrlem2f.e
    lclkrlem2f.g
    ldualvaddcom
    #
    fveq1d
    lclkrlem2f.kb
    eqtr3d
    wph
    cX
    cB
    csn
    c.pe
    cfv
    #
    wcel
    wn
    cY
    @7
    wcel
    wn
    lclkrlem2f.nx
    orcomd
    lclkrlem2k.y
    lclkrlem2k.x
    lclkrlem2j
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
    @8
    3eqtr4d
end
