include "csn.mm"
include "cfv.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "clss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lssss.mm"
include "syl.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "syl5eqr.mm"
include "wb.mm"
include "cbs.mm"
include "crg.mm"
include "lmodring.mm"
include "ldualvaddcl.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "cdr.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "drnginvrcl.mm"
include "ringcl.mm"
include "lmodvscl.mm"
include "lmodsubeq0.mm"
include "mpbid.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "lspsnvsi.mm"
include "eqsstrd.mm"
include "dochss.mm"
include "snssd.mm"
include "dochocsp.mm"
include "3sstr3d.mm"

theorem lclkrlem2p
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
  assume lclkrlem2p.bn: |- ( ph -> B = ( 0g ` U ) )


  assert |- ( ph -> ( ._|_ ` { Y } ) C_ ( ._|_ ` { X } ) )

  proof
    wph
    cY
    csn
    #
    cN
    cfv
    #
    c.pe
    cfv
    #
    cX
    csn
    #
    cN
    cfv
    #
    c.pe
    cfv
    #
    @0
    c.pe
    cfv
    @3
    c.pe
    cfv
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @1
    cV
    wss
    #
    @4
    @1
    wss
    @2
    @5
    wss
    lclkrlem2o.k
    wph
    @1
    cU
    clss
    cfv
    #
    wcel
    #
    @6
    wph
    cU
    clmod
    wcel
    #
    cY
    cV
    wcel
    #
    @8
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
    lclkrlem2m.y
    @7
    cN
    cV
    cU
    cY
    lclkrlem2m.v
    @7
    eqid
    #
    lclkrlem2n.n
    lspsncl
    syl2anc
    @7
    @1
    cV
    cU
    lclkrlem2m.v
    @12
    lssss
    syl
    wph
    @4
    cX
    cE
    cG
    c.pl
    co
    #
    cfv
    #
    cY
    @13
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
    csn
    #
    cN
    cfv
    #
    @1
    wph
    @3
    @19
    cN
    wph
    cX
    @18
    wph
    cX
    @18
    c.mi
    co
    #
    cU
    c0g
    cfv
    #
    wceq
    #
    cX
    @18
    wceq
    #
    wph
    @21
    cB
    @22
    lclkrlem2o.b
    lclkrlem2p.bn
    syl5eqr
    wph
    @9
    cX
    cV
    wcel
    #
    @18
    cV
    wcel
    #
    @23
    @24
    wb
    @11
    lclkrlem2m.x
    wph
    @9
    @17
    cS
    cbs
    cfv
    #
    wcel
    #
    @10
    @26
    @11
    wph
    cS
    crg
    wcel
    #
    @14
    @27
    wcel
    #
    @16
    @27
    wcel
    #
    @28
    wph
    @9
    @29
    @11
    cS
    cU
    lclkrlem2m.s
    lmodring
    syl
    wph
    @9
    @13
    cF
    wcel
    #
    @25
    @30
    @11
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
    @11
    lclkrlem2m.e
    lclkrlem2m.g
    ldualvaddcl
    #
    lclkrlem2m.x
    cS
    cF
    @13
    @27
    cV
    cU
    cX
    clmod
    lclkrlem2m.s
    @27
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
    @15
    @27
    wcel
    #
    @15
    c.0
    wne
    @31
    wph
    cU
    clvec
    wcel
    @35
    wph
    cU
    cH
    cK
    cW
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2o.k
    dvhlvec
    cS
    cU
    lclkrlem2m.s
    lvecdrng
    syl
    wph
    @9
    @32
    @10
    @36
    @11
    @33
    lclkrlem2m.y
    cS
    cF
    @13
    @27
    cV
    cU
    cY
    clmod
    lclkrlem2m.s
    @34
    lclkrlem2m.v
    lclkrlem2m.f
    lflcl
    syl3anc
    lclkrlem2o.n
    @27
    cS
    cI
    @15
    c.0
    @34
    lclkrlem2m.z
    lclkrlem2m.i
    drnginvrcl
    syl3anc
    @27
    cS
    c.xp
    @14
    @16
    @34
    lclkrlem2m.q
    ringcl
    syl3anc
    #
    lclkrlem2m.y
    @17
    c.x
    cS
    @27
    cV
    cU
    cY
    lclkrlem2m.v
    lclkrlem2m.s
    lclkrlem2m.t
    @34
    lmodvscl
    syl3anc
    cX
    @18
    c.mi
    cV
    cU
    @22
    lclkrlem2m.v
    @22
    eqid
    lclkrlem2m.m
    lmodsubeq0
    syl3anc
    mpbid
    sneqd
    fveq2d
    wph
    @9
    @28
    @10
    @20
    @1
    wss
    @11
    @37
    lclkrlem2m.y
    @17
    c.x
    cS
    @27
    cN
    cV
    cU
    cY
    lclkrlem2m.s
    @34
    lclkrlem2m.v
    lclkrlem2m.t
    lclkrlem2n.n
    lspsnvsi
    syl3anc
    eqsstrd
    cU
    cH
    cK
    c.pe
    cV
    cW
    @4
    @1
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2m.v
    lclkrlem2o.o
    dochss
    syl3anc
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    @0
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2o.o
    lclkrlem2m.v
    lclkrlem2n.n
    lclkrlem2o.k
    wph
    cY
    cV
    lclkrlem2m.y
    snssd
    dochocsp
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    @3
    lclkrlem2o.h
    lclkrlem2o.u
    lclkrlem2o.o
    lclkrlem2m.v
    lclkrlem2n.n
    lclkrlem2o.k
    wph
    cX
    cV
    lclkrlem2m.x
    snssd
    dochocsp
    3sstr3d
end
