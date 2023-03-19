include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wo.mm"
include "simpr.mm"
include "lclkrlem2k.mm"
include "lclkrlem2j.mm"
include "wne.mm"
include "simprl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simprr.mm"
include "lclkrlem2i.mm"
include "pm2.61da2ne.mm"

theorem lclkrlem2l
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
  assume lclkrlem2l.x: |- ( ph -> X e. V )
  assume lclkrlem2l.y: |- ( ph -> Y e. V )


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
    c.0
    cY
    c.0
    wph
    cX
    c.0
    wceq
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
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @2
    lclkrlem2f.k
    adantr
    wph
    cB
    cV
    c.0
    csn
    cdif
    #
    wcel
    #
    @2
    lclkrlem2f.b
    adantr
    wph
    cE
    cF
    wcel
    #
    @2
    lclkrlem2f.e
    adantr
    wph
    cG
    cF
    wcel
    #
    @2
    lclkrlem2f.g
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
    @2
    lclkrlem2f.le
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
    @2
    lclkrlem2f.lg
    adantr
    wph
    cB
    @0
    cfv
    cQ
    wceq
    #
    @2
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
    @11
    wcel
    wn
    wo
    #
    @2
    lclkrlem2f.nx
    adantr
    wph
    @2
    simpr
    wph
    cY
    cV
    wcel
    #
    @2
    lclkrlem2l.y
    adantr
    lclkrlem2k
    wph
    cY
    c.0
    wceq
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
    @3
    @14
    lclkrlem2f.k
    adantr
    wph
    @5
    @14
    lclkrlem2f.b
    adantr
    wph
    @6
    @14
    lclkrlem2f.e
    adantr
    wph
    @7
    @14
    lclkrlem2f.g
    adantr
    wph
    @8
    @14
    lclkrlem2f.le
    adantr
    wph
    @9
    @14
    lclkrlem2f.lg
    adantr
    wph
    @10
    @14
    lclkrlem2f.kb
    adantr
    wph
    @12
    @14
    lclkrlem2f.nx
    adantr
    wph
    cX
    cV
    wcel
    #
    @14
    lclkrlem2l.x
    adantr
    wph
    @14
    simpr
    lclkrlem2j
    wph
    cX
    c.0
    wne
    #
    cY
    c.0
    wne
    #
    wa
    #
    wa
    #
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
    @3
    @18
    lclkrlem2f.k
    adantr
    wph
    @5
    @18
    lclkrlem2f.b
    adantr
    wph
    @6
    @18
    lclkrlem2f.e
    adantr
    wph
    @7
    @18
    lclkrlem2f.g
    adantr
    wph
    @8
    @18
    lclkrlem2f.le
    adantr
    wph
    @9
    @18
    lclkrlem2f.lg
    adantr
    wph
    @10
    @18
    lclkrlem2f.kb
    adantr
    wph
    @12
    @18
    lclkrlem2f.nx
    adantr
    @19
    @15
    @16
    cX
    @4
    wcel
    wph
    @15
    @18
    lclkrlem2l.x
    adantr
    wph
    @16
    @17
    simprl
    cX
    cV
    c.0
    eldifsn
    sylanbrc
    @19
    @13
    @17
    cY
    @4
    wcel
    wph
    @13
    @18
    lclkrlem2l.y
    adantr
    wph
    @16
    @17
    simprr
    cY
    cV
    c.0
    eldifsn
    sylanbrc
    lclkrlem2i
    pm2.61da2ne
end
