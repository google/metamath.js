include "csn.mm"
include "cfv.mm"
include "co.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdih.mm"
include "crn.mm"
include "wceq.mm"
include "wss.mm"
include "snssd.mm"
include "eqid.mm"
include "dochcl.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "c0g.mm"
include "cbs.mm"
include "cxp.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "doch0.mm"
include "syl.mm"
include "3eqtrd.mm"
include "clmod.mm"
include "wb.mm"
include "dvhlmod.mm"
include "lkr0f.mm"
include "mpbid.mm"
include "ldual0v.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "lduallmod.mm"
include "ldualelvbase.mm"
include "lmod0vrid.mm"
include "eqtrd.mm"
include "eqtr2d.mm"
include "3eqtr3d.mm"

theorem lclkrlem2j
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
  assume lclkrlem2j.x: |- ( ph -> X e. V )
  assume lclkrlem2j.y: |- ( ph -> Y = .0. )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` ( E .+ G ) ) ) ) = ( L ` ( E .+ G ) ) )

  proof
    wph
    cX
    csn
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
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
    @5
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @3
    @1
    wceq
    lclkrlem2f.k
    wph
    @7
    @0
    cV
    wss
    @9
    lclkrlem2f.k
    wph
    cX
    cV
    lclkrlem2j.x
    snssd
    cU
    cH
    @8
    cK
    c.pe
    cV
    cW
    @0
    lclkrlem2f.h
    @8
    eqid
    #
    lclkrlem2f.u
    lclkrlem2f.v
    lclkrlem2f.o
    dochcl
    syl2anc
    cH
    @8
    cK
    c.pe
    cW
    @1
    lclkrlem2f.h
    @10
    lclkrlem2f.o
    dochoc
    syl2anc
    wph
    @2
    @6
    c.pe
    wph
    @1
    @5
    c.pe
    wph
    @5
    cE
    cL
    cfv
    @1
    wph
    @4
    cE
    cL
    wph
    @4
    cE
    cD
    c0g
    cfv
    #
    c.pl
    co
    #
    cE
    wph
    cG
    @11
    cE
    c.pl
    wph
    cG
    cU
    cbs
    cfv
    #
    cQ
    csn
    cxp
    #
    @11
    wph
    cG
    cL
    cfv
    #
    @13
    wceq
    #
    cG
    @14
    wceq
    #
    wph
    @15
    cY
    csn
    #
    c.pe
    cfv
    c.0
    csn
    #
    c.pe
    cfv
    #
    @13
    lclkrlem2f.lg
    wph
    @18
    @19
    c.pe
    wph
    cY
    c.0
    lclkrlem2j.y
    sneqd
    fveq2d
    wph
    @7
    @20
    @13
    wceq
    lclkrlem2f.k
    cU
    cH
    cK
    c.pe
    @13
    cW
    c.0
    lclkrlem2f.h
    lclkrlem2f.u
    lclkrlem2f.o
    @13
    eqid
    #
    lclkrlem2f.z
    doch0
    syl
    3eqtrd
    wph
    cU
    clmod
    wcel
    cG
    cF
    wcel
    @16
    @17
    wb
    wph
    cU
    cH
    cK
    cW
    lclkrlem2f.h
    lclkrlem2f.u
    lclkrlem2f.k
    dvhlmod
    #
    lclkrlem2f.g
    cS
    cF
    cG
    cL
    @13
    cU
    cQ
    lclkrlem2f.s
    lclkrlem2f.q
    @21
    lclkrlem2f.f
    lclkrlem2f.l
    lkr0f
    syl2anc
    mpbid
    wph
    cD
    cS
    @11
    @13
    cU
    cQ
    @21
    lclkrlem2f.s
    lclkrlem2f.q
    lclkrlem2f.d
    @11
    eqid
    #
    @22
    ldual0v
    eqtr4d
    oveq2d
    wph
    cD
    clmod
    wcel
    cE
    cD
    cbs
    cfv
    #
    wcel
    @12
    cE
    wceq
    wph
    cD
    cU
    lclkrlem2f.d
    @22
    lduallmod
    wph
    cD
    cF
    cE
    @24
    cU
    clmod
    lclkrlem2f.f
    lclkrlem2f.d
    @24
    eqid
    #
    @22
    lclkrlem2f.e
    ldualelvbase
    c.pl
    @24
    cD
    cE
    @11
    @25
    lclkrlem2f.p
    @23
    lmod0vrid
    syl2anc
    eqtrd
    fveq2d
    lclkrlem2f.le
    eqtr2d
    #
    fveq2d
    fveq2d
    @26
    3eqtr3d
end
