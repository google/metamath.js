include "co.mm"
include "cfv.mm"
include "cdih.mm"
include "crn.mm"
include "wcel.mm"
include "wceq.mm"
include "cin.mm"
include "csn.mm"
include "wss.mm"
include "lclkrlem2f.mm"
include "dvhlvec.mm"
include "ineq12d.mm"
include "oveq1d.mm"
include "clsa.mm"
include "eqid.mm"
include "3netr3d.mm"
include "lclkrlem2c.mm"
include "eqeltrd.mm"
include "lshpcmp.mm"
include "mpbid.mm"
include "lclkrlem2d.mm"
include "eqeltrrd.mm"
include "chlt.mm"
include "wa.mm"
include "dihrnss.mm"
include "syl2anc.mm"
include "dochoccl.mm"

theorem lclkrlem2g
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
  assume lclkrlem2f.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lclkrlem2f.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lclkrlem2f.ne: |- ( ph -> ( L ` E ) =/= ( L ` G ) )
  assume lclkrlem2f.lp: |- ( ph -> ( L ` ( E .+ G ) ) e. J )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` ( E .+ G ) ) ) ) = ( L ` ( E .+ G ) ) )

  proof
    wph
    cE
    cG
    c.pl
    co
    cL
    cfv
    #
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    #
    wcel
    #
    @0
    c.pe
    cfv
    c.pe
    cfv
    @0
    wceq
    wph
    cE
    cL
    cfv
    #
    cG
    cL
    cfv
    #
    cin
    #
    cB
    csn
    cN
    cfv
    #
    c.po
    co
    #
    @0
    @2
    wph
    @8
    @0
    wss
    @8
    @0
    wceq
    wph
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
    lclkrlem2f.k
    lclkrlem2f.b
    lclkrlem2f.e
    lclkrlem2f.g
    lclkrlem2f.le
    lclkrlem2f.lg
    lclkrlem2f.kb
    lclkrlem2f.nx
    lclkrlem2f.x
    lclkrlem2f.y
    lclkrlem2f.ne
    lclkrlem2f.lp
    lclkrlem2f
    wph
    @8
    @0
    cJ
    cU
    lclkrlem2f.j
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
    @8
    cX
    csn
    c.pe
    cfv
    #
    cY
    csn
    c.pe
    cfv
    #
    cin
    #
    @7
    c.po
    co
    #
    cJ
    wph
    @6
    @11
    @7
    c.po
    wph
    @4
    @9
    @5
    @10
    lclkrlem2f.le
    lclkrlem2f.lg
    ineq12d
    oveq1d
    #
    wph
    cU
    clsa
    cfv
    #
    cB
    c.po
    cU
    cH
    cJ
    cK
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
    lclkrlem2f.z
    lclkrlem2f.a
    lclkrlem2f.n
    @14
    eqid
    #
    lclkrlem2f.k
    lclkrlem2f.b
    lclkrlem2f.x
    lclkrlem2f.y
    wph
    @4
    @5
    @9
    @10
    lclkrlem2f.ne
    lclkrlem2f.le
    lclkrlem2f.lg
    3netr3d
    #
    lclkrlem2f.nx
    lclkrlem2f.j
    lclkrlem2c
    eqeltrd
    lclkrlem2f.lp
    lshpcmp
    mpbid
    wph
    @8
    @12
    @2
    @13
    wph
    @14
    cB
    c.po
    cU
    cH
    @1
    cK
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
    lclkrlem2f.z
    lclkrlem2f.a
    lclkrlem2f.n
    @15
    lclkrlem2f.k
    lclkrlem2f.b
    lclkrlem2f.x
    lclkrlem2f.y
    @16
    lclkrlem2f.nx
    @1
    eqid
    #
    lclkrlem2d
    eqeltrd
    eqeltrrd
    #
    wph
    cU
    cH
    @1
    cK
    c.pe
    cV
    cW
    @0
    lclkrlem2f.h
    @17
    lclkrlem2f.u
    lclkrlem2f.v
    lclkrlem2f.o
    lclkrlem2f.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @3
    @0
    cV
    wss
    lclkrlem2f.k
    @18
    cU
    cH
    @1
    cK
    cV
    cW
    @0
    lclkrlem2f.h
    lclkrlem2f.u
    @17
    lclkrlem2f.v
    dihrnss
    syl2anc
    dochoccl
    mpbid
end
