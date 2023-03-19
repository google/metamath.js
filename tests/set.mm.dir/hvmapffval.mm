include "wcel.mm"
include "cvv.mm"
include "chvm.mm"
include "cfv.mm"
include "cv.mm"
include "cdvh.mm"
include "cbs.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "wceq.mm"
include "coch.mm"
include "wrex.mm"
include "csca.mm"
include "crio.mm"
include "cmpt.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
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
include "df-hvmap.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem hvmapffval
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let vj: setvar j
  let cH: class H
  let cK: class K
  let cX: class X
  let vk: setvar k
  let cW: class W
  assume hvmapval.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint j t
  disjoint j v
  disjoint j x
  disjoint j w
  disjoint K j
  disjoint t v
  disjoint t x
  disjoint t w
  disjoint K t
  disjoint v x
  disjoint v w
  disjoint K v
  disjoint w x
  disjoint K x
  disjoint K w
  disjoint k w
  disjoint H k
  disjoint j k
  disjoint k t
  disjoint k v
  disjoint k x
  disjoint K k
  disjoint W t
  assert |- ( K e. X -> ( HVMap ` K ) = ( w e. H |-> ( x e. ( ( Base ` ( ( DVecH ` K ) ` w ) ) \ { ( 0g ` ( ( DVecH ` K ) ` w ) ) } ) |-> ( v e. ( Base ` ( ( DVecH ` K ) ` w ) ) |-> ( iota_ j e. ( Base ` ( Scalar ` ( ( DVecH ` K ) ` w ) ) ) E. t e. ( ( ( ocH ` K ) ` w ) ` { x } ) v = ( t ( +g ` ( ( DVecH ` K ) ` w ) ) ( j ( .s ` ( ( DVecH ` K ) ` w ) ) x ) ) ) ) ) ) )

  proof
    cK
    cX
    wcel
    cK
    cvv
    wcel
    cK
    chvm
    cfv
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
    @2
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    vv
    @3
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
    @2
    cvsca
    cfv
    #
    co
    #
    @2
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vt
    @10
    csn
    #
    @0
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
    @2
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
    wceq
    cK
    cX
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    vx
    @0
    @27
    cdvh
    cfv
    #
    cfv
    #
    cbs
    cfv
    #
    @30
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    vv
    @31
    @7
    @8
    @9
    @10
    @30
    cvsca
    cfv
    #
    co
    #
    @30
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vt
    @16
    @0
    @27
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
    @30
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
    @26
    cvv
    chvm
    @27
    cK
    wceq
    #
    vw
    @28
    @48
    cH
    @25
    @49
    @28
    cK
    clh
    cfv
    #
    cH
    @27
    cK
    clh
    fveq2
    hvmapval.h
    syl6eqr
    @49
    vx
    @34
    @47
    @6
    @24
    @49
    @31
    @3
    @33
    @5
    @49
    @30
    @2
    cbs
    @49
    @0
    @29
    @1
    @27
    cK
    cdvh
    fveq2
    fveq1d
    #
    fveq2d
    #
    @49
    @32
    @4
    @49
    @30
    @2
    c0g
    @51
    fveq2d
    sneqd
    difeq12d
    @49
    vv
    @31
    @46
    @3
    @23
    @52
    @49
    @43
    @20
    vj
    @45
    @22
    @49
    @44
    @21
    cbs
    @49
    @30
    @2
    csca
    @51
    fveq2d
    fveq2d
    @49
    @39
    @15
    vt
    @42
    @19
    @49
    @16
    @41
    @18
    @49
    @0
    @40
    @17
    @27
    cK
    coch
    fveq2
    fveq1d
    fveq1d
    @49
    @38
    @14
    @7
    @49
    @8
    @8
    @36
    @12
    @37
    @13
    @49
    @30
    @2
    cplusg
    @51
    fveq2d
    @49
    @8
    eqidd
    @49
    @35
    @11
    @9
    @10
    @49
    @30
    @2
    cvsca
    @51
    fveq2d
    oveqd
    oveq123d
    eqeq2d
    rexeqbidv
    riotaeqbidv
    mpteq12dv
    mpteq12dv
    mpteq12dv
    vx
    vw
    vv
    vt
    vj
    vk
    df-hvmap
    vw
    cH
    @25
    cH
    @50
    cvv
    hvmapval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
