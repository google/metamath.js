include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "cdvh.mm"
include "cbs.mm"
include "c0g.mm"
include "cvsca.mm"
include "cplusg.mm"
include "coch.mm"
include "csca.mm"
include "chvm.mm"
include "hvmapffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "eqidd.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "eqeq2d.mm"
include "rexeqbidv.mm"
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "ax-mp.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "syl.mm"

theorem hvmapfval
  let wph: wff ph
  let vx: setvar x
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vj: setvar j
  let cH: class H
  let cK: class K
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  let vw: setvar w
  assume hvmapval.h: |- H = ( LHyp ` K )
  assume hvmapval.u: |- U = ( ( DVecH ` K ) ` W )
  assume hvmapval.o: |- O = ( ( ocH ` K ) ` W )
  assume hvmapval.v: |- V = ( Base ` U )
  assume hvmapval.p: |- .+ = ( +g ` U )
  assume hvmapval.t: |- .x. = ( .s ` U )
  assume hvmapval.z: |- .0. = ( 0g ` U )
  assume hvmapval.s: |- S = ( Scalar ` U )
  assume hvmapval.r: |- R = ( Base ` S )
  assume hvmapval.m: |- M = ( ( HVMap ` K ) ` W )
  assume hvmapval.k: |- ( ph -> ( K e. A /\ W e. H ) )

  disjoint j t
  disjoint j v
  disjoint j x
  disjoint K j
  disjoint t v
  disjoint t x
  disjoint K t
  disjoint v x
  disjoint K v
  disjoint K x
  disjoint W t
  disjoint O t
  disjoint R j
  disjoint V x
  disjoint W j
  disjoint W v
  disjoint W x
  disjoint .0. x
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint j k
  disjoint j w
  disjoint k t
  disjoint k v
  disjoint k x
  disjoint K k
  disjoint t w
  disjoint v w
  disjoint w x
  disjoint K w
  disjoint O w
  disjoint .+ w
  disjoint R w
  disjoint .x. w
  disjoint V w
  disjoint W w
  disjoint .0. w
  assert |- ( ph -> M = ( x e. ( V \ { .0. } ) |-> ( v e. V |-> ( iota_ j e. R E. t e. ( O ` { x } ) v = ( t .+ ( j .x. x ) ) ) ) ) )

  proof
    wph
    cK
    cA
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    cM
    vx
    cV
    c.0
    csn
    #
    cdif
    #
    vv
    cV
    vv
    cv
    #
    vt
    cv
    #
    vj
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vt
    @7
    csn
    #
    cO
    cfv
    #
    wrex
    #
    vj
    cR
    crio
    #
    cmpt
    #
    cmpt
    #
    wceq
    hvmapval.k
    @0
    @1
    cM
    cW
    vw
    cH
    vx
    vw
    cv
    #
    cK
    cdvh
    cfv
    #
    cfv
    #
    cbs
    cfv
    #
    @19
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    vv
    @20
    @4
    @5
    @6
    @7
    @19
    cvsca
    cfv
    #
    co
    #
    @19
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vt
    @11
    @17
    cK
    coch
    cfv
    #
    cfv
    #
    cfv
    #
    wrex
    #
    vj
    @19
    csca
    cfv
    #
    cbs
    cfv
    #
    crio
    #
    cmpt
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    @16
    @0
    cM
    cW
    cK
    chvm
    cfv
    #
    cfv
    @39
    hvmapval.m
    @0
    cW
    @40
    @38
    vx
    vw
    vv
    vt
    vj
    cH
    cK
    cA
    hvmapval.h
    hvmapffval
    fveq1d
    syl5eq
    vw
    cW
    @37
    @16
    cH
    @38
    @17
    cW
    wceq
    #
    vx
    @23
    @36
    @3
    @15
    @41
    @20
    cV
    @22
    @2
    @41
    @20
    cU
    cbs
    cfv
    #
    cV
    @41
    @19
    cU
    cbs
    @41
    @19
    cW
    @18
    cfv
    cU
    @17
    cW
    @18
    fveq2
    hvmapval.u
    syl6eqr
    #
    fveq2d
    hvmapval.v
    syl6eqr
    #
    @41
    @21
    c.0
    @41
    @21
    cU
    c0g
    cfv
    c.0
    @41
    @19
    cU
    c0g
    @43
    fveq2d
    hvmapval.z
    syl6eqr
    sneqd
    difeq12d
    @41
    vv
    @20
    @35
    cV
    @14
    @44
    @41
    @32
    @13
    vj
    @34
    cR
    @41
    @34
    cS
    cbs
    cfv
    cR
    @41
    @33
    cS
    cbs
    @41
    @33
    cU
    csca
    cfv
    cS
    @41
    @19
    cU
    csca
    @43
    fveq2d
    hvmapval.s
    syl6eqr
    fveq2d
    hvmapval.r
    syl6eqr
    @41
    @28
    @10
    vt
    @31
    @12
    @41
    @11
    @30
    cO
    @41
    @30
    cW
    @29
    cfv
    cO
    @17
    cW
    @29
    fveq2
    hvmapval.o
    syl6eqr
    fveq1d
    @41
    @27
    @9
    @4
    @41
    @5
    @5
    @25
    @8
    @26
    c.pl
    @41
    @26
    cU
    cplusg
    cfv
    c.pl
    @41
    @19
    cU
    cplusg
    @43
    fveq2d
    hvmapval.p
    syl6eqr
    @41
    @5
    eqidd
    @41
    @24
    c.x
    @6
    @7
    @41
    @24
    cU
    cvsca
    cfv
    c.x
    @41
    @19
    cU
    cvsca
    @43
    fveq2d
    hvmapval.t
    syl6eqr
    oveqd
    oveq123d
    eqeq2d
    rexeqbidv
    riotaeqbidv
    mpteq12dv
    mpteq12dv
    @38
    eqid
    vx
    @3
    @15
    cV
    cvv
    wcel
    @3
    cvv
    wcel
    cV
    @42
    cvv
    hvmapval.v
    cU
    cbs
    fvex
    eqeltri
    cV
    @2
    cvv
    difexg
    ax-mp
    mptex
    fvmpt
    sylan9eq
    syl
end
