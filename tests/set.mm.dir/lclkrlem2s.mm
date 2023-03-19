include "cfv.mm"
include "clsh.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "chlt.mm"
include "cdih.mm"
include "crn.mm"
include "wss.mm"
include "snssd.mm"
include "eqid.mm"
include "dochcl.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "ad2antrr.mm"
include "lclkrlem2r.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "simplr.mm"
include "simpr.mm"
include "lshpcmp.mm"
include "mpbid.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "dochoc1.mm"
include "wo.mm"
include "dvhlmod.mm"
include "ldualvaddcl.mm"
include "lkrshpor.mm"
include "adantr.mm"
include "mpjaodan.mm"
include "lkrssv.mm"
include "eqsstr3d.mm"
include "eqssd.mm"

theorem lclkrlem2s
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


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` ( E .+ G ) ) ) ) = ( L ` ( E .+ G ) ) )

  proof
    wph
    cG
    cL
    cfv
    #
    cU
    clsh
    cfv
    #
    wcel
    #
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
    #
    @4
    wceq
    #
    @0
    cV
    wceq
    #
    wph
    @2
    wa
    #
    @4
    @1
    wcel
    #
    @7
    @4
    cV
    wceq
    #
    @9
    @10
    wa
    #
    cY
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
    @14
    @6
    @4
    wph
    @16
    @14
    wceq
    #
    @2
    @10
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @14
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @17
    lclkrlem2o.k
    wph
    @18
    @13
    cV
    wss
    @20
    lclkrlem2o.k
    wph
    cY
    cV
    lclkrlem2m.y
    snssd
    cU
    cH
    @19
    cK
    c.pe
    cV
    cW
    @13
    lclkrlem2o.h
    @19
    eqid
    #
    lclkrlem2o.u
    lclkrlem2m.v
    lclkrlem2o.o
    dochcl
    syl2anc
    cH
    @19
    cK
    c.pe
    cW
    @14
    lclkrlem2o.h
    @21
    lclkrlem2o.o
    dochoc
    syl2anc
    ad2antrr
    @12
    @5
    @15
    c.pe
    @12
    @4
    @14
    c.pe
    @12
    @0
    @4
    @14
    @12
    @0
    @4
    wss
    #
    @0
    @4
    wceq
    wph
    @22
    @2
    @10
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
    lclkrlem2q.le
    lclkrlem2q.lg
    lclkrlem2q.b
    lclkrlem2q.n
    lclkrlem2r.bn
    lclkrlem2r
    #
    ad2antrr
    @12
    @0
    @4
    @1
    cU
    @1
    eqid
    #
    wph
    cU
    clvec
    wcel
    @2
    @10
    wph
    cU
    cH
    cK
    cW
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2o.k
    dvhlvec
    #
    ad2antrr
    wph
    @2
    @10
    simplr
    @9
    @10
    simpr
    lshpcmp
    mpbid
    wph
    @0
    @14
    wceq
    @2
    @10
    lclkrlem2q.lg
    ad2antrr
    eqtr3d
    #
    fveq2d
    fveq2d
    @26
    3eqtr4d
    @9
    @11
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
    @6
    @4
    wph
    @29
    cV
    wceq
    #
    @2
    @11
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2o.o
    lclkrlem2m.v
    lclkrlem2o.k
    dochoc1
    #
    ad2antrr
    @27
    @5
    @28
    c.pe
    @27
    @4
    cV
    c.pe
    @9
    @11
    simpr
    #
    fveq2d
    fveq2d
    @32
    3eqtr4d
    wph
    @10
    @11
    wo
    @2
    wph
    cF
    @3
    @1
    cL
    cV
    cU
    lclkrlem2m.v
    @24
    lclkrlem2m.f
    lclkrlem2n.l
    @25
    wph
    cD
    c.pl
    cF
    cE
    cG
    cU
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
    #
    lclkrlem2m.e
    lclkrlem2m.g
    ldualvaddcl
    #
    lkrshpor
    adantr
    mpjaodan
    wph
    @8
    wa
    #
    @29
    cV
    @6
    @4
    wph
    @30
    @8
    @31
    adantr
    @35
    @5
    @28
    c.pe
    @35
    @4
    cV
    c.pe
    @35
    @4
    cV
    wph
    @4
    cV
    wss
    @8
    wph
    cF
    @3
    cL
    cV
    cU
    lclkrlem2m.v
    lclkrlem2m.f
    lclkrlem2n.l
    @33
    @34
    lkrssv
    adantr
    @35
    cV
    @0
    @4
    wph
    @8
    simpr
    wph
    @22
    @8
    @23
    adantr
    eqsstr3d
    eqssd
    #
    fveq2d
    fveq2d
    @36
    3eqtr4d
    wph
    cF
    cG
    @1
    cL
    cV
    cU
    lclkrlem2m.v
    @24
    lclkrlem2m.f
    lclkrlem2n.l
    @25
    lclkrlem2m.g
    lkrshpor
    mpjaodan
end
