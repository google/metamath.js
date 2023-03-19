include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "wa.mm"
include "wcel.mm"
include "adantr.mm"
include "chlt.mm"
include "csn.mm"
include "eqid.mm"
include "wne.mm"
include "simpr.mm"
include "lclkrlem2s.mm"
include "lclkrlem2q.mm"
include "pm2.61dane.mm"

theorem lclkrlem2t
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
  assume lclkrlem2t.n: |- ( ph -> ( ( E .+ G ) ` Y ) =/= .0. )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` ( E .+ G ) ) ) ) = ( L ` ( E .+ G ) ) )

  proof
    wph
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
    c.pe
    cfv
    @1
    wceq
    cX
    cX
    @0
    cfv
    cY
    @0
    cfv
    #
    cI
    cfv
    c.xp
    co
    cY
    c.x
    co
    c.mi
    co
    #
    cU
    c0g
    cfv
    #
    wph
    @3
    @4
    wceq
    #
    wa
    @3
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
    wph
    cX
    cV
    wcel
    #
    @5
    lclkrlem2m.x
    adantr
    wph
    cY
    cV
    wcel
    #
    @5
    lclkrlem2m.y
    adantr
    wph
    cE
    cF
    wcel
    #
    @5
    lclkrlem2m.e
    adantr
    wph
    cG
    cF
    wcel
    #
    @5
    lclkrlem2m.g
    adantr
    lclkrlem2n.n
    lclkrlem2n.l
    lclkrlem2o.h
    lclkrlem2o.o
    lclkrlem2o.u
    lclkrlem2o.a
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @5
    lclkrlem2o.k
    adantr
    wph
    cE
    cL
    cfv
    cX
    csn
    c.pe
    cfv
    wceq
    #
    @5
    lclkrlem2q.le
    adantr
    wph
    cG
    cL
    cfv
    cY
    csn
    c.pe
    cfv
    wceq
    #
    @5
    lclkrlem2q.lg
    adantr
    @3
    eqid
    #
    wph
    @2
    c.0
    wne
    #
    @5
    lclkrlem2t.n
    adantr
    wph
    @5
    simpr
    lclkrlem2s
    wph
    @3
    @4
    wne
    #
    wa
    @3
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
    wph
    @6
    @15
    lclkrlem2m.x
    adantr
    wph
    @7
    @15
    lclkrlem2m.y
    adantr
    wph
    @8
    @15
    lclkrlem2m.e
    adantr
    wph
    @9
    @15
    lclkrlem2m.g
    adantr
    lclkrlem2n.n
    lclkrlem2n.l
    lclkrlem2o.h
    lclkrlem2o.o
    lclkrlem2o.u
    lclkrlem2o.a
    wph
    @10
    @15
    lclkrlem2o.k
    adantr
    wph
    @11
    @15
    lclkrlem2q.le
    adantr
    wph
    @12
    @15
    lclkrlem2q.lg
    adantr
    @13
    wph
    @14
    @15
    lclkrlem2t.n
    adantr
    wph
    @15
    simpr
    lclkrlem2q
    pm2.61dane
end
