include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "simpr.mm"
include "lclkrlem2e.mm"
include "wne.mm"
include "wn.mm"
include "wo.mm"
include "lclkrlem2h.mm"
include "pm2.61dane.mm"

theorem lclkrlem2i
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
  assume lclkrlem2i.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lclkrlem2i.y: |- ( ph -> Y e. ( V \ { .0. } ) )


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
    cE
    cL
    cfv
    #
    cG
    cL
    cfv
    #
    wph
    @2
    @3
    wceq
    #
    wa
    cD
    c.pl
    cU
    cE
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lclkrlem2f.h
    lclkrlem2f.o
    lclkrlem2f.u
    lclkrlem2f.v
    lclkrlem2f.z
    lclkrlem2f.f
    lclkrlem2f.l
    lclkrlem2f.d
    lclkrlem2f.p
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @4
    lclkrlem2f.k
    adantr
    wph
    cX
    cV
    c.0
    csn
    cdif
    #
    wcel
    #
    @4
    lclkrlem2i.x
    adantr
    wph
    cE
    cF
    wcel
    #
    @4
    lclkrlem2f.e
    adantr
    wph
    cG
    cF
    wcel
    #
    @4
    lclkrlem2f.g
    adantr
    wph
    @2
    cX
    csn
    c.pe
    cfv
    wceq
    #
    @4
    lclkrlem2f.le
    adantr
    wph
    @4
    simpr
    lclkrlem2e
    wph
    @2
    @3
    wne
    #
    wa
    cB
    cD
    c.pl
    c.po
    cQ
    cS
    cU
    cE
    cF
    cG
    cH
    cJ
    cK
    cL
    cN
    c.pe
    cV
    cW
    cX
    cY
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
    wph
    @5
    @11
    lclkrlem2f.k
    adantr
    wph
    cB
    @6
    wcel
    @11
    lclkrlem2f.b
    adantr
    wph
    @8
    @11
    lclkrlem2f.e
    adantr
    wph
    @9
    @11
    lclkrlem2f.g
    adantr
    wph
    @10
    @11
    lclkrlem2f.le
    adantr
    wph
    @3
    cY
    csn
    c.pe
    cfv
    wceq
    @11
    lclkrlem2f.lg
    adantr
    wph
    cB
    @0
    cfv
    cQ
    wceq
    @11
    lclkrlem2f.kb
    adantr
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
    @12
    wcel
    wn
    wo
    @11
    lclkrlem2f.nx
    adantr
    wph
    @7
    @11
    lclkrlem2i.x
    adantr
    wph
    cY
    @6
    wcel
    @11
    lclkrlem2i.y
    adantr
    wph
    @11
    simpr
    lclkrlem2h
    pm2.61dane
end
