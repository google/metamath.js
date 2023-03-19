include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wo.mm"
include "wne.mm"
include "simpr.mm"
include "lclkrlem2g.mm"
include "dochoc1.mm"
include "dvhlvec.mm"
include "dvhlmod.mm"
include "ldualvaddcl.mm"
include "lkrshpor.mm"
include "orcanai.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "pm2.61dan.mm"

theorem lclkrlem2h
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
  assume lclkrlem2h.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lclkrlem2h.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lclkrlem2h.ne: |- ( ph -> ( L ` E ) =/= ( L ` G ) )


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
    cJ
    wcel
    #
    @1
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @1
    wceq
    wph
    @2
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
    @2
    lclkrlem2f.b
    adantr
    wph
    cE
    cF
    wcel
    @2
    lclkrlem2f.e
    adantr
    wph
    cG
    cF
    wcel
    @2
    lclkrlem2f.g
    adantr
    wph
    cE
    cL
    cfv
    #
    cX
    csn
    c.pe
    cfv
    wceq
    @2
    lclkrlem2f.le
    adantr
    wph
    cG
    cL
    cfv
    #
    cY
    csn
    c.pe
    cfv
    wceq
    @2
    lclkrlem2f.lg
    adantr
    wph
    cB
    @0
    cfv
    cQ
    wceq
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
    @8
    wcel
    wn
    wo
    @2
    lclkrlem2f.nx
    adantr
    wph
    cX
    @5
    wcel
    @2
    lclkrlem2h.x
    adantr
    wph
    cY
    @5
    wcel
    @2
    lclkrlem2h.y
    adantr
    wph
    @6
    @7
    wne
    @2
    lclkrlem2h.ne
    adantr
    wph
    @2
    simpr
    lclkrlem2g
    wph
    @2
    wn
    #
    wa
    #
    cV
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cV
    @4
    @1
    wph
    @12
    cV
    wceq
    @9
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    lclkrlem2f.h
    lclkrlem2f.u
    lclkrlem2f.o
    lclkrlem2f.v
    lclkrlem2f.k
    dochoc1
    adantr
    @10
    @3
    @11
    c.pe
    @10
    @1
    cV
    c.pe
    wph
    @2
    @1
    cV
    wceq
    wph
    cF
    @0
    cJ
    cL
    cV
    cU
    lclkrlem2f.v
    lclkrlem2f.j
    lclkrlem2f.f
    lclkrlem2f.l
    wph
    cU
    cH
    cK
    cW
    lclkrlem2f.h
    lclkrlem2f.u
    lclkrlem2f.k
    dvhlvec
    wph
    cD
    c.pl
    cF
    cE
    cG
    cU
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
    ldualvaddcl
    lkrshpor
    orcanai
    #
    fveq2d
    fveq2d
    @13
    3eqtr4d
    pm2.61dan
end
