include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "c0g.mm"
include "eqid.mm"
include "wne.mm"
include "cdif.mm"
include "co.mm"
include "wceq.mm"
include "dvhlvec.mm"
include "lclkrlem2m.mm"
include "simpld.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "dochnel.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "adantr.mm"
include "chlt.mm"
include "wss.mm"
include "snssd.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "simprl.mm"
include "cbs.mm"
include "crg.mm"
include "lmodring.mm"
include "syl.mm"
include "ldualvaddcl.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "cdr.mm"
include "clvec.mm"
include "lvecdrng.mm"
include "drnginvrcl.mm"
include "ringcl.mm"
include "simprr.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "lssvsubcl.mm"
include "syl5eqel.mm"
include "mtand.mm"
include "ianor.mm"
include "sylib.mm"

theorem lclkrlem2o
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
  assume lclkrlem2o.b: |- B = ( X .- ( ( ( ( E .+ G ) ` X ) .X. ( I ` ( ( E .+ G ) ` Y ) ) ) .x. Y ) )
  assume lclkrlem2o.n: |- ( ph -> ( ( E .+ G ) ` Y ) =/= .0. )
  assume lclkrlem2o.bn: |- ( ph -> B =/= ( 0g ` U ) )


  assert |- ( ph -> ( -. X e. ( ._|_ ` { B } ) \/ -. Y e. ( ._|_ ` { B } ) ) )

  proof
    wph
    cX
    cB
    csn
    #
    c.pe
    cfv
    #
    wcel
    #
    cY
    @1
    wcel
    #
    wa
    #
    wn
    @2
    wn
    @3
    wn
    wo
    wph
    @4
    cB
    @1
    wcel
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    cB
    cU
    c0g
    cfv
    #
    lclkrlem2o.h
    lclkrlem2o.o
    lclkrlem2o.u
    lclkrlem2m.v
    @5
    eqid
    lclkrlem2o.k
    wph
    cB
    cV
    wcel
    #
    cB
    @5
    wne
    cB
    cV
    @5
    csn
    cdif
    wcel
    wph
    @6
    cB
    cE
    cG
    c.pl
    co
    #
    cfv
    c.0
    wceq
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
    #
    lclkrlem2o.b
    lclkrlem2o.n
    lclkrlem2m
    simpld
    #
    lclkrlem2o.bn
    cB
    cV
    @5
    eldifsn
    sylanbrc
    dochnel
    wph
    @4
    wa
    #
    cB
    cX
    cX
    @7
    cfv
    #
    cY
    @7
    cfv
    #
    cI
    cfv
    #
    c.xp
    co
    #
    cY
    c.x
    co
    #
    c.mi
    co
    #
    @1
    lclkrlem2o.b
    @10
    cU
    clmod
    wcel
    #
    @1
    cU
    clss
    cfv
    #
    wcel
    #
    @2
    @15
    @1
    wcel
    #
    @16
    @1
    wcel
    wph
    @17
    @4
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
    adantr
    #
    wph
    @19
    @4
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @0
    cV
    wss
    @19
    lclkrlem2o.k
    wph
    cB
    cV
    @9
    snssd
    @18
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2m.v
    @18
    eqid
    #
    lclkrlem2o.o
    dochlss
    syl2anc
    adantr
    #
    wph
    @2
    @3
    simprl
    @10
    @17
    @19
    @14
    cS
    cbs
    cfv
    #
    wcel
    #
    @3
    @20
    @22
    @24
    wph
    @26
    @4
    wph
    cS
    crg
    wcel
    #
    @11
    @25
    wcel
    #
    @13
    @25
    wcel
    #
    @26
    wph
    @17
    @27
    @21
    cS
    cU
    lclkrlem2m.s
    lmodring
    syl
    wph
    @17
    @7
    cF
    wcel
    #
    cX
    cV
    wcel
    @28
    @21
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
    @21
    lclkrlem2m.e
    lclkrlem2m.g
    ldualvaddcl
    #
    lclkrlem2m.x
    cS
    cF
    @7
    @25
    cV
    cU
    cX
    clmod
    lclkrlem2m.s
    @25
    eqid
    #
    lclkrlem2m.v
    lclkrlem2m.f
    lflcl
    syl3anc
    wph
    cS
    cdr
    wcel
    #
    @12
    @25
    wcel
    #
    @12
    c.0
    wne
    @29
    wph
    cU
    clvec
    wcel
    @33
    @8
    cS
    cU
    lclkrlem2m.s
    lvecdrng
    syl
    wph
    @17
    @30
    cY
    cV
    wcel
    @34
    @21
    @31
    lclkrlem2m.y
    cS
    cF
    @7
    @25
    cV
    cU
    cY
    clmod
    lclkrlem2m.s
    @32
    lclkrlem2m.v
    lclkrlem2m.f
    lflcl
    syl3anc
    lclkrlem2o.n
    @25
    cS
    cI
    @12
    c.0
    @32
    lclkrlem2m.z
    lclkrlem2m.i
    drnginvrcl
    syl3anc
    @25
    cS
    c.xp
    @11
    @13
    @32
    lclkrlem2m.q
    ringcl
    syl3anc
    adantr
    wph
    @2
    @3
    simprr
    @25
    @18
    c.x
    @1
    cS
    cU
    @14
    cY
    lclkrlem2m.s
    lclkrlem2m.t
    @32
    @23
    lssvscl
    syl22anc
    @18
    @1
    c.mi
    cU
    cX
    @15
    lclkrlem2m.m
    @23
    lssvsubcl
    syl22anc
    syl5eqel
    mtand
    @2
    @3
    ianor
    sylib
end
